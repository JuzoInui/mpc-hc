/*
 * (C) 2003-2006 Gabest
 * (C) 2006-2018 see Authors.txt
 *
 * This file is part of MPC-HC.
 *
 * MPC-HC is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * MPC-HC is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include "stdafx.h"
#include "MainFrm.h"
#include "mplayerc.h"
#include "version.h"

#include "GraphThread.h"
#include "FGFilterLAV.h"
#include "FGManager.h"
#include "FGManagerBDA.h"
#include "ShockwaveGraph.h"
#include "TextPassThruFilter.h"
#include "FakeFilterMapper2.h"

#include "ColorControlsDlg.h"
#include "FavoriteAddDlg.h"
#include "GoToDlg.h"
#include "HistoryDlg.h"
#include "MediaTypesDlg.h"
#include "OpenFileDlg.h"
#include "PnSPresetsDlg.h"
#include "SaveDlg.h"
#include "SaveImageDialog.h"
#include "SaveSubtitlesFileDialog.h"
#include "SaveThumbnailsDialog.h"
#include "OpenDirHelper.h"
#include "OpenDlg.h"
#include "TunerScanDlg.h"

#include "ComPropertySheet.h"
#include "PPageAccelTbl.h"
#include "PPageAudioSwitcher.h"
#include "PPageFileInfoSheet.h"
#include "PPageSheet.h"
#include "PPageSubStyle.h"
#include "PPageSubtitles.h"

#include "CoverArt.h"
#include "CrashReporter.h"
#include "KeyProvider.h"
#include "Translations.h"
#include "UpdateChecker.h"
#include "WebServer.h"
#include <ISOLang.h>
#include <PathUtils.h>
#include <DSUtil.h>

#include "../DeCSS/VobFile.h"
#include "../SubPic/DualSubPicProvider.h"
#include "../Subtitles/PGSSub.h"
#include "../Subtitles/RLECodedSubtitle.h"
#include "../Subtitles/RTS.h"
#include "../Subtitles/STS.h"
#include <SubRenderIntf.h>

#include "../filters/InternalPropertyPage.h"
#include "../filters/PinInfoWnd.h"
#include "../filters/renderer/SyncClock/SyncClock.h"
#include "../filters/transform/BufferFilter/BufferFilter.h"

#include <AllocatorCommon.h>
#include <NullRenderers.h>
#include <RARFileSource/RFS.h>
#include <SyncAllocatorPresenter.h>

#include "FullscreenWnd.h"
#include "Monitors.h"

#include <WinAPIUtils.h>
#include <WinapiFunc.h>
#include <moreuuids.h>

#include <IBitRateInfo.h>
#include <IChapterInfo.h>
#include <IPinHook.h>

#include <mvrInterfaces.h>

#include <Il21dec.h>
#include <dvdevcod.h>
#include <dvdmedia.h>
#include <strsafe.h>
#include <VersionHelpersInternal.h>

#include <initguid.h>
#include <qnetwork.h>

#include "YoutubeDL.h"
#include "CMPCThemeMenu.h"
#include "CMPCThemeDockBar.h"
#include "CMPCThemeMiniDockFrameWnd.h"
#include "RarEntrySelectorDialog.h"
#include "FileHandle.h"
#include "MPCFolderPickerDialog.h"

#include "stb/stb_image.h"
#include "stb/stb_image_resize2.h"
#include "stb/stb_image_write.h"

#include  "Logger.h"

#include <dwmapi.h>
#undef SubclassWindow

// IID_IAMLine21Decoder
DECLARE_INTERFACE_IID_(IAMLine21Decoder_2, IAMLine21Decoder, "6E8D4A21-310C-11d0-B79A-00AA003767A7") {};

#define MIN_LOGO_WIDTH 360
#define MIN_LOGO_HEIGHT 150

#define PREV_CHAP_THRESHOLD 2

static UINT s_uTaskbarRestart = RegisterWindowMessage(_T("TaskbarCreated"));
static UINT WM_NOTIFYICON = RegisterWindowMessage(_T("MYWM_NOTIFYICON"));
static UINT s_uTBBC = RegisterWindowMessage(_T("TaskbarButtonCreated"));
static UINT WM_MPCAPI_INT = RegisterWindowMessage(MPCAPI_INT_MESSAGE_NAME);

CMainFrame::PlaybackRateMap CMainFrame::filePlaybackRates = {
    { ID_PLAY_PLAYBACKRATE_025,  .25f},
    { ID_PLAY_PLAYBACKRATE_050,  .50f},
    { ID_PLAY_PLAYBACKRATE_075,  .75f},
    { ID_PLAY_PLAYBACKRATE_090,  .90f},
    { ID_PLAY_PLAYBACKRATE_100, 1.00f},
    { ID_PLAY_PLAYBACKRATE_110, 1.10f},
    { ID_PLAY_PLAYBACKRATE_125, 1.25f},
    { ID_PLAY_PLAYBACKRATE_150, 1.50f},
    { ID_PLAY_PLAYBACKRATE_175, 1.75f},
    { ID_PLAY_PLAYBACKRATE_200, 2.00f},
    { ID_PLAY_PLAYBACKRATE_300, 3.00f},
    { ID_PLAY_PLAYBACKRATE_400, 4.00f},
    { ID_PLAY_PLAYBACKRATE_600, 6.00f},
    { ID_PLAY_PLAYBACKRATE_800, 8.00f},
};

CMainFrame::PlaybackRateMap CMainFrame::dvdPlaybackRates = {
    { ID_PLAY_PLAYBACKRATE_025,  .25f},
    { ID_PLAY_PLAYBACKRATE_050,  .50f},
    { ID_PLAY_PLAYBACKRATE_100, 1.00f},
    { ID_PLAY_PLAYBACKRATE_200, 2.00f},
    { ID_PLAY_PLAYBACKRATE_400, 4.00f},
    { ID_PLAY_PLAYBACKRATE_800, 8.00f},
};


static bool EnsureDirectory(CString directory)
{
    int ret = SHCreateDirectoryEx(nullptr, directory, nullptr);
    bool result = ret == ERROR_SUCCESS || ret == ERROR_ALREADY_EXISTS;
    if (!result) {
        AfxMessageBox(_T("Cannot create directory: ") + directory, MB_ICONEXCLAMATION | MB_OK);
    }
    return result;
}

class CSubClock : public CUnknown, public ISubClock
{
    STDMETHODIMP NonDelegatingQueryInterface(REFIID riid, void** ppv) {
        return
            QI(ISubClock)
            CUnknown::NonDelegatingQueryInterface(riid, ppv);
    }

    REFERENCE_TIME m_rt;

public:
    CSubClock() : CUnknown(NAME("CSubClock"), nullptr) {
        m_rt = 0;
    }

    DECLARE_IUNKNOWN;

    // ISubClock
    STDMETHODIMP SetTime(REFERENCE_TIME rt) {
        m_rt = rt;
        return S_OK;
    }
    STDMETHODIMP_(REFERENCE_TIME) GetTime() {
        return m_rt;
    }
};

bool FileFavorite::TryParse(const CString& fav, FileFavorite& ff)
{
    CAtlList<CString> parts;
    return TryParse(fav, ff, parts);
}

bool FileFavorite::TryParse(const CString& fav, FileFavorite& ff, CAtlList<CString>& parts)
{
    ExplodeEsc(fav, parts, _T(';'));
    if (parts.IsEmpty()) {
        return false;
    }

    ff.Name = parts.RemoveHead();

    if (!parts.IsEmpty()) {
        // Start position and optional A-B marks "pos[:A:B]"
        auto startPos = parts.RemoveHead();
        _stscanf_s(startPos, _T("%I64d:%I64d:%I64d"), &ff.Start, &ff.MarkA, &ff.MarkB);
        ff.Start = std::max(ff.Start, 0ll); // Sanitize
    }
    if (!parts.IsEmpty()) {
        _stscanf_s(parts.RemoveHead(), _T("%d"), &ff.RelativeDrive);
    }
    return true;
}

CString FileFavorite::ToString() const
{
    CString str;
    if (RelativeDrive) {
        str = _T("[RD]");
    }
    if (Start > 0) {    // Start position
        str.AppendFormat(_T("[%s]"), ReftimeToString2(Start).GetString());
    }
    if (MarkA > 0 || MarkB > 0) {   // A-B marks (only characters to save space)
        CString abMarks;
        if (MarkA > 0) {
            abMarks = _T("A");
        }
        if (MarkB > 0) {
            abMarks.Append(_T("-B"));
        }
        str.AppendFormat(_T("[%s]"), abMarks.GetString());
    }
    return str;
}

/////////////////////////////////////////////////////////////////////////////
// CMainFrame

IMPLEMENT_DYNAMIC(CMainFrame, CFrameWnd)

BEGIN_MESSAGE_MAP(CMainFrame, CFrameWnd)
    ON_WM_NCCREATE()
    ON_WM_CREATE()
    ON_WM_DESTROY()
    ON_WM_CLOSE()
    ON_MESSAGE(WM_LAV_PROPPAGE_CALLBACK, OnLAVPropPageCallback)
    ON_WM_MEASUREITEM()

    ON_MESSAGE(WM_MPCVR_SWITCH_FULLSCREEN, OnMPCVRSwitchFullscreen)

    ON_REGISTERED_MESSAGE(s_uTaskbarRestart, OnTaskBarRestart)
    ON_REGISTERED_MESSAGE(WM_NOTIFYICON, OnNotifyIcon)

    ON_REGISTERED_MESSAGE(s_uTBBC, OnTaskBarThumbnailsCreate)
    ON_REGISTERED_MESSAGE(WM_MPCAPI_INT, OnApiIntMessage)

    ON_WM_SETFOCUS()
    ON_WM_GETMINMAXINFO()
    ON_WM_MOVE()
    ON_WM_ENTERSIZEMOVE()
    ON_WM_MOVING()
    ON_WM_SIZE()
    ON_WM_SHOWWINDOW()
    ON_WM_SIZING()
    ON_WM_EXITSIZEMOVE()
    ON_MESSAGE_VOID(WM_DISPLAYCHANGE, OnDisplayChange)
    ON_WM_WINDOWPOSCHANGING()

    ON_MESSAGE(WM_DPICHANGED, OnDpiChanged)

    ON_WM_SYSCOMMAND()
    ON_WM_ACTIVATEAPP()
    ON_MESSAGE(WM_APPCOMMAND, OnAppCommand)
    ON_WM_INPUT()
    ON_MESSAGE(WM_HOTKEY, OnHotKey)

    ON_WM_TIMER()

    ON_MESSAGE(WM_GRAPHNOTIFY, OnGraphNotify)
    ON_MESSAGE(WM_RESET_DEVICE, OnResetDevice)
    ON_MESSAGE(WM_REARRANGERENDERLESS, OnRepaintRenderLess)

    ON_MESSAGE(WM_MPC_STANDBY, OnDoStandby)
    ON_MESSAGE(WM_MPC_HIBERNATE, OnDoHibernate)
    ON_MESSAGE(WM_MPC_SHUTDOWN, OnDoShutdown)
    ON_MESSAGE(WM_MPC_LOGOFF, OnDoLogOff)
    ON_MESSAGE(WM_MPC_OPENCURPLAYLIST, OnDoOpenCurPlaylist)

    ON_MESSAGE(WM_SMTC_SEEK, OnSmtcSeek)
    ON_MESSAGE(WM_SMTC_AUTOREPEAT, OnSmtcAutoRepeat)
    ON_MESSAGE(WM_SMTC_SHUFFLE, OnSmtcShuffle)
    ON_MESSAGE(WM_SMTC_RATE, OnSmtcRate)

    ON_MESSAGE_VOID(WM_SAVESETTINGS, SaveAppSettings)

    ON_WM_NCHITTEST()

    ON_WM_HSCROLL()

    ON_WM_INITMENU()
    ON_WM_INITMENUPOPUP()
    ON_WM_UNINITMENUPOPUP()

    ON_WM_ENTERMENULOOP()

    ON_WM_QUERYENDSESSION()
    ON_WM_ENDSESSION()

    ON_COMMAND(ID_MENU_PLAYER_SHORT, OnMenuPlayerShort)
    ON_COMMAND(ID_MENU_PLAYER_LONG, OnMenuPlayerLong)
    ON_COMMAND(ID_MENU_FILTERS, OnMenuFilters)

    ON_UPDATE_COMMAND_UI(IDC_PLAYERSTATUS, OnUpdatePlayerStatus)

    ON_MESSAGE(WM_POSTOPEN, OnFilePostOpenmedia)
    ON_MESSAGE(WM_OPENFAILED, OnOpenMediaFailed)
    ON_MESSAGE(WM_TUNER_NEW_CHANNEL, OnHeadlessScanNewChannel)
    ON_MESSAGE(WM_TUNER_SCAN_END, OnHeadlessScanEnd)
    ON_MESSAGE(WM_DVB_EIT_DATA_READY, OnCurrentChannelInfoUpdated)

    ON_COMMAND(ID_BOSS, OnBossKey)

    ON_COMMAND_RANGE(ID_STREAM_AUDIO_NEXT, ID_STREAM_AUDIO_PREV, OnStreamAudio)
    ON_COMMAND_RANGE(ID_STREAM_SUB_NEXT, ID_STREAM_SUB_PREV, OnStreamSub)
    ON_COMMAND(ID_AUDIOSHIFT_ONOFF, OnAudioShiftOnOff)
    ON_COMMAND(ID_STREAM_SUB_ONOFF, OnStreamSubOnOff)
    ON_COMMAND(ID_SUBTITLES_AUTOCOPY, OnSubtitlesAutoCopy)
    ON_COMMAND_RANGE(ID_DVD_ANGLE_NEXT, ID_DVD_ANGLE_PREV, OnDvdAngle)
    ON_COMMAND_RANGE(ID_DVD_AUDIO_NEXT, ID_DVD_AUDIO_PREV, OnDvdAudio)
    ON_COMMAND_RANGE(ID_DVD_SUB_NEXT, ID_DVD_SUB_PREV, OnDvdSub)
    ON_COMMAND(ID_DVD_SUB_ONOFF, OnDvdSubOnOff)

    ON_COMMAND(ID_FILE_OPENQUICK, OnFileOpenQuick)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPENMEDIA, OnUpdateFileOpen)
    ON_COMMAND(ID_FILE_OPENMEDIA, OnFileOpenmedia)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPENMEDIA, OnUpdateFileOpen)
    ON_WM_COPYDATA()
    ON_COMMAND(ID_FILE_OPENDVDBD, OnFileOpendvd)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPENDVDBD, OnUpdateFileOpen)
    ON_COMMAND(ID_FILE_OPENDEVICE, OnFileOpendevice)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPENDEVICE, OnUpdateFileOpen)
    ON_COMMAND_RANGE(ID_FILE_OPEN_OPTICAL_DISK_START, ID_FILE_OPEN_OPTICAL_DISK_END, OnFileOpenOpticalDisk)
    ON_UPDATE_COMMAND_UI_RANGE(ID_FILE_OPEN_OPTICAL_DISK_START, ID_FILE_OPEN_OPTICAL_DISK_END, OnUpdateFileOpen)
    ON_COMMAND(ID_FILE_REOPEN, OnFileReopen)
    ON_COMMAND(ID_FILE_RECYCLE, OnFileRecycle)
    ON_COMMAND(ID_FILE_SAVE_COPY, OnFileSaveAs)
    ON_UPDATE_COMMAND_UI(ID_FILE_SAVE_COPY, OnUpdateFileSaveAs)
    ON_COMMAND(ID_FILE_SAVE_IMAGE, OnFileSaveImage)
    ON_UPDATE_COMMAND_UI(ID_FILE_SAVE_IMAGE, OnUpdateFileSaveImage)
    ON_COMMAND(ID_FILE_SAVE_IMAGE_AUTO, OnFileSaveImageAuto)
    ON_UPDATE_COMMAND_UI(ID_FILE_SAVE_IMAGE_AUTO, OnUpdateFileSaveImage)
    ON_COMMAND(ID_CMDLINE_SAVE_THUMBNAILS, OnCmdLineSaveThumbnails)
    ON_COMMAND(ID_FILE_SAVE_THUMBNAILS, OnFileSaveThumbnails)
    ON_UPDATE_COMMAND_UI(ID_FILE_SAVE_THUMBNAILS, OnUpdateFileSaveThumbnails)
    ON_COMMAND(ID_FILE_SUBTITLES_LOAD, OnFileSubtitlesLoad)
    ON_UPDATE_COMMAND_UI(ID_FILE_SUBTITLES_LOAD, OnUpdateFileSubtitlesLoad)
    ON_COMMAND(ID_FILE_SUBTITLES_SAVE, OnFileSubtitlesSave)
    ON_UPDATE_COMMAND_UI(ID_FILE_SUBTITLES_SAVE, OnUpdateFileSubtitlesSave)
    //ON_COMMAND(ID_FILE_SUBTITLES_UPLOAD, OnFileSubtitlesUpload)
    //ON_UPDATE_COMMAND_UI(ID_FILE_SUBTITLES_UPLOAD, OnUpdateFileSubtitlesUpload)
    ON_COMMAND(ID_FILE_SUBTITLES_DOWNLOAD, OnFileSubtitlesDownload)
    ON_UPDATE_COMMAND_UI(ID_FILE_SUBTITLES_DOWNLOAD, OnUpdateFileSubtitlesDownload)
    ON_COMMAND(ID_FILE_PROPERTIES, OnFileProperties)
    ON_UPDATE_COMMAND_UI(ID_FILE_PROPERTIES, OnUpdateFileProperties)
    ON_COMMAND(ID_FILE_OPEN_LOCATION, OnFileOpenLocation)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPEN_LOCATION, OnUpdateFileProperties)
    ON_COMMAND(ID_FILE_CLOSE_AND_RESTORE, OnFileCloseAndRestore)
    ON_UPDATE_COMMAND_UI(ID_FILE_CLOSE_AND_RESTORE, OnUpdateFileClose)
    ON_COMMAND(ID_FILE_CLOSEMEDIA, OnFileCloseMedia)
    ON_UPDATE_COMMAND_UI(ID_FILE_CLOSEMEDIA, OnUpdateFileClose)

    ON_COMMAND(ID_VIEW_CAPTIONMENU, OnViewCaptionmenu)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CAPTIONMENU, OnUpdateViewCaptionmenu)
    ON_COMMAND_RANGE(ID_VIEW_SEEKER, ID_VIEW_STATUS, OnViewControlBar)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VIEW_SEEKER, ID_VIEW_STATUS, OnUpdateViewControlBar)
    ON_COMMAND(ID_VIEW_SUBRESYNC, OnViewSubresync)
    ON_UPDATE_COMMAND_UI(ID_VIEW_SUBRESYNC, OnUpdateViewSubresync)
    ON_COMMAND(ID_VIEW_PLAYLIST, OnViewPlaylist)
    ON_UPDATE_COMMAND_UI(ID_VIEW_PLAYLIST, OnUpdateViewPlaylist)
    ON_COMMAND(ID_PLAYLIST_TOGGLE_SHUFFLE, OnPlaylistToggleShuffle)
    ON_COMMAND(ID_VIEW_EDITLISTEDITOR, OnViewEditListEditor)
    ON_COMMAND(ID_EDL_IN, OnEDLIn)
    ON_UPDATE_COMMAND_UI(ID_EDL_IN, OnUpdateEDLIn)
    ON_COMMAND(ID_EDL_OUT, OnEDLOut)
    ON_UPDATE_COMMAND_UI(ID_EDL_OUT, OnUpdateEDLOut)
    ON_COMMAND(ID_EDL_NEWCLIP, OnEDLNewClip)
    ON_UPDATE_COMMAND_UI(ID_EDL_NEWCLIP, OnUpdateEDLNewClip)
    ON_COMMAND(ID_EDL_SAVE, OnEDLSave)
    ON_UPDATE_COMMAND_UI(ID_EDL_SAVE, OnUpdateEDLSave)
    ON_COMMAND(ID_VIEW_CAPTURE, OnViewCapture)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CAPTURE, OnUpdateViewCapture)
    ON_COMMAND(ID_VIEW_DEBUGSHADERS, OnViewDebugShaders)
    ON_UPDATE_COMMAND_UI(ID_VIEW_DEBUGSHADERS, OnUpdateViewDebugShaders)
    ON_COMMAND(ID_COLOR_CONTROLS, OnViewColorControls)
    ON_UPDATE_COMMAND_UI(ID_COLOR_CONTROLS, OnUpdateViewColorControls)
    ON_COMMAND(ID_VIEW_PRESETS_MINIMAL, OnViewMinimal)
    ON_UPDATE_COMMAND_UI(ID_VIEW_PRESETS_MINIMAL, OnUpdateViewMinimal)
    ON_COMMAND(ID_VIEW_PRESETS_COMPACT, OnViewCompact)
    ON_UPDATE_COMMAND_UI(ID_VIEW_PRESETS_COMPACT, OnUpdateViewCompact)
    ON_COMMAND(ID_VIEW_PRESETS_NORMAL, OnViewNormal)
    ON_UPDATE_COMMAND_UI(ID_VIEW_PRESETS_NORMAL, OnUpdateViewNormal)
    ON_COMMAND(ID_VIEW_PRESETS_CUSTOM, OnViewCustom)
    ON_UPDATE_COMMAND_UI(ID_VIEW_PRESETS_CUSTOM, OnUpdateViewCustom)
    ON_COMMAND(ID_VIEW_FULLSCREEN, OnViewFullscreen)
    ON_COMMAND(ID_VIEW_FULLSCREEN_SECONDARY, OnViewFullscreenSecondary)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FULLSCREEN, OnUpdateViewFullscreen)
    ON_COMMAND_RANGE(ID_VIEW_ZOOM_50, ID_VIEW_ZOOM_200, OnViewZoom)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VIEW_ZOOM_50, ID_VIEW_ZOOM_200, OnUpdateViewZoom)
    ON_COMMAND_RANGE(ID_VIEW_ZOOM_25, ID_VIEW_ZOOM_25, OnViewZoom)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VIEW_ZOOM_25, ID_VIEW_ZOOM_25, OnUpdateViewZoom)
    ON_COMMAND(ID_VIEW_ZOOM_AUTOFIT, OnViewZoomAutoFit)
    ON_UPDATE_COMMAND_UI(ID_VIEW_ZOOM_AUTOFIT, OnUpdateViewZoom)
    ON_COMMAND(ID_VIEW_ZOOM_AUTOFIT_LARGER, OnViewZoomAutoFitLarger)
    ON_UPDATE_COMMAND_UI(ID_VIEW_ZOOM_AUTOFIT_LARGER, OnUpdateViewZoom)
    ON_COMMAND_RANGE(ID_VIEW_ZOOM_SUB, ID_VIEW_ZOOM_ADD, OnViewModifySize)
    ON_COMMAND_RANGE(ID_VIEW_VF_HALF, ID_VIEW_VF_ZOOM2, OnViewDefaultVideoFrame)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VIEW_VF_HALF, ID_VIEW_VF_ZOOM2, OnUpdateViewDefaultVideoFrame)
    ON_COMMAND(ID_VIEW_VF_SWITCHZOOM, OnViewSwitchVideoFrame)
    ON_COMMAND(ID_VIEW_VF_COMPMONDESKARDIFF, OnViewCompMonDeskARDiff)
    ON_UPDATE_COMMAND_UI(ID_VIEW_VF_COMPMONDESKARDIFF, OnUpdateViewCompMonDeskARDiff)
    ON_COMMAND_RANGE(ID_VIEW_RESET, ID_PANSCAN_CENTER, OnViewPanNScan)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VIEW_RESET, ID_PANSCAN_CENTER, OnUpdateViewPanNScan)
    ON_COMMAND_RANGE(ID_PANNSCAN_PRESETS_START, ID_PANNSCAN_PRESETS_END, OnViewPanNScanPresets)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PANNSCAN_PRESETS_START, ID_PANNSCAN_PRESETS_END, OnUpdateViewPanNScanPresets)
    ON_COMMAND_RANGE(ID_PANSCAN_ROTATEXP, ID_PANSCAN_ROTATEZM, OnViewRotate)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PANSCAN_ROTATEXP, ID_PANSCAN_ROTATEZM, OnUpdateViewRotate)
    ON_COMMAND_RANGE(ID_PANSCAN_ROTATEZ270_OLD, ID_PANSCAN_ROTATEZ270_OLD, OnViewRotate)
    ON_COMMAND_RANGE(ID_PANSCAN_ROTATEZP2, ID_PANSCAN_ROTATEZP2, OnViewRotate)
    ON_COMMAND_RANGE(ID_ASPECTRATIO_START, ID_ASPECTRATIO_END, OnViewAspectRatio)
    ON_UPDATE_COMMAND_UI_RANGE(ID_ASPECTRATIO_START, ID_ASPECTRATIO_END, OnUpdateViewAspectRatio)
    ON_COMMAND(ID_ASPECTRATIO_NEXT, OnViewAspectRatioNext)
    ON_COMMAND_RANGE(ID_ONTOP_DEFAULT, ID_ONTOP_WHILEPLAYINGVIDEO, OnViewOntop)
    ON_UPDATE_COMMAND_UI_RANGE(ID_ONTOP_DEFAULT, ID_ONTOP_WHILEPLAYINGVIDEO, OnUpdateViewOntop)
    ON_COMMAND(ID_VIEW_OPTIONS, OnViewOptions)

    // Casimir666
    ON_UPDATE_COMMAND_UI(ID_VIEW_TEARING_TEST, OnUpdateViewTearingTest)
    ON_COMMAND(ID_VIEW_TEARING_TEST, OnViewTearingTest)
    ON_UPDATE_COMMAND_UI(ID_VIEW_DISPLAY_RENDERER_STATS, OnUpdateViewDisplayRendererStats)
    ON_COMMAND(ID_VIEW_RESET_RENDERER_STATS, OnViewResetRendererStats)
    ON_COMMAND(ID_VIEW_DISPLAY_RENDERER_STATS, OnViewDisplayRendererStats)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FULLSCREENGUISUPPORT, OnUpdateViewFullscreenGUISupport)
    ON_UPDATE_COMMAND_UI(ID_VIEW_HIGHCOLORRESOLUTION, OnUpdateViewHighColorResolution)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FORCEINPUTHIGHCOLORRESOLUTION, OnUpdateViewForceInputHighColorResolution)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FULLFLOATINGPOINTPROCESSING, OnUpdateViewFullFloatingPointProcessing)
    ON_UPDATE_COMMAND_UI(ID_VIEW_HALFFLOATINGPOINTPROCESSING, OnUpdateViewHalfFloatingPointProcessing)
    ON_UPDATE_COMMAND_UI(ID_VIEW_ENABLEFRAMETIMECORRECTION, OnUpdateViewEnableFrameTimeCorrection)
    ON_UPDATE_COMMAND_UI(ID_VIEW_VSYNC, OnUpdateViewVSync)
    ON_UPDATE_COMMAND_UI(ID_VIEW_VSYNCOFFSET, OnUpdateViewVSyncOffset)
    ON_UPDATE_COMMAND_UI(ID_VIEW_VSYNCACCURATE, OnUpdateViewVSyncAccurate)

    ON_UPDATE_COMMAND_UI(ID_VIEW_SYNCHRONIZEVIDEO, OnUpdateViewSynchronizeVideo)
    ON_UPDATE_COMMAND_UI(ID_VIEW_SYNCHRONIZEDISPLAY, OnUpdateViewSynchronizeDisplay)
    ON_UPDATE_COMMAND_UI(ID_VIEW_SYNCHRONIZENEAREST, OnUpdateViewSynchronizeNearest)

    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_ENABLE, OnUpdateViewColorManagementEnable)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INPUT_AUTO, OnUpdateViewColorManagementInput)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INPUT_HDTV, OnUpdateViewColorManagementInput)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INPUT_SDTV_NTSC, OnUpdateViewColorManagementInput)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INPUT_SDTV_PAL, OnUpdateViewColorManagementInput)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_AMBIENTLIGHT_BRIGHT, OnUpdateViewColorManagementAmbientLight)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_AMBIENTLIGHT_DIM, OnUpdateViewColorManagementAmbientLight)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_AMBIENTLIGHT_DARK, OnUpdateViewColorManagementAmbientLight)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INTENT_PERCEPTUAL, OnUpdateViewColorManagementIntent)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INTENT_RELATIVECOLORIMETRIC, OnUpdateViewColorManagementIntent)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INTENT_SATURATION, OnUpdateViewColorManagementIntent)
    ON_UPDATE_COMMAND_UI(ID_VIEW_CM_INTENT_ABSOLUTECOLORIMETRIC, OnUpdateViewColorManagementIntent)

    ON_UPDATE_COMMAND_UI(ID_VIEW_EVROUTPUTRANGE_0_255, OnUpdateViewEVROutputRange)
    ON_UPDATE_COMMAND_UI(ID_VIEW_EVROUTPUTRANGE_16_235, OnUpdateViewEVROutputRange)

    ON_UPDATE_COMMAND_UI(ID_VIEW_FLUSHGPU_BEFOREVSYNC, OnUpdateViewFlushGPU)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FLUSHGPU_AFTERPRESENT, OnUpdateViewFlushGPU)
    ON_UPDATE_COMMAND_UI(ID_VIEW_FLUSHGPU_WAIT, OnUpdateViewFlushGPU)

    ON_UPDATE_COMMAND_UI(ID_VIEW_D3DFULLSCREEN, OnUpdateViewD3DFullscreen)
    ON_UPDATE_COMMAND_UI(ID_VIEW_DISABLEDESKTOPCOMPOSITION, OnUpdateViewDisableDesktopComposition)
    ON_UPDATE_COMMAND_UI(ID_VIEW_ALTERNATIVEVSYNC, OnUpdateViewAlternativeVSync)

    ON_UPDATE_COMMAND_UI(ID_VIEW_VSYNCOFFSET_INCREASE, OnUpdateViewVSyncOffsetIncrease)
    ON_UPDATE_COMMAND_UI(ID_VIEW_VSYNCOFFSET_DECREASE, OnUpdateViewVSyncOffsetDecrease)
    ON_COMMAND(ID_VIEW_FULLSCREENGUISUPPORT, OnViewFullscreenGUISupport)
    ON_COMMAND(ID_VIEW_HIGHCOLORRESOLUTION, OnViewHighColorResolution)
    ON_COMMAND(ID_VIEW_FORCEINPUTHIGHCOLORRESOLUTION, OnViewForceInputHighColorResolution)
    ON_COMMAND(ID_VIEW_FULLFLOATINGPOINTPROCESSING, OnViewFullFloatingPointProcessing)
    ON_COMMAND(ID_VIEW_HALFFLOATINGPOINTPROCESSING, OnViewHalfFloatingPointProcessing)
    ON_COMMAND(ID_VIEW_ENABLEFRAMETIMECORRECTION, OnViewEnableFrameTimeCorrection)
    ON_COMMAND(ID_VIEW_VSYNC, OnViewVSync)
    ON_COMMAND(ID_VIEW_VSYNCACCURATE, OnViewVSyncAccurate)

    ON_COMMAND(ID_VIEW_SYNCHRONIZEVIDEO, OnViewSynchronizeVideo)
    ON_COMMAND(ID_VIEW_SYNCHRONIZEDISPLAY, OnViewSynchronizeDisplay)
    ON_COMMAND(ID_VIEW_SYNCHRONIZENEAREST, OnViewSynchronizeNearest)

    ON_COMMAND(ID_VIEW_CM_ENABLE, OnViewColorManagementEnable)
    ON_COMMAND(ID_VIEW_CM_INPUT_AUTO, OnViewColorManagementInputAuto)
    ON_COMMAND(ID_VIEW_CM_INPUT_HDTV, OnViewColorManagementInputHDTV)
    ON_COMMAND(ID_VIEW_CM_INPUT_SDTV_NTSC, OnViewColorManagementInputSDTV_NTSC)
    ON_COMMAND(ID_VIEW_CM_INPUT_SDTV_PAL, OnViewColorManagementInputSDTV_PAL)
    ON_COMMAND(ID_VIEW_CM_AMBIENTLIGHT_BRIGHT, OnViewColorManagementAmbientLightBright)
    ON_COMMAND(ID_VIEW_CM_AMBIENTLIGHT_DIM, OnViewColorManagementAmbientLightDim)
    ON_COMMAND(ID_VIEW_CM_AMBIENTLIGHT_DARK, OnViewColorManagementAmbientLightDark)
    ON_COMMAND(ID_VIEW_CM_INTENT_PERCEPTUAL, OnViewColorManagementIntentPerceptual)
    ON_COMMAND(ID_VIEW_CM_INTENT_RELATIVECOLORIMETRIC, OnViewColorManagementIntentRelativeColorimetric)
    ON_COMMAND(ID_VIEW_CM_INTENT_SATURATION, OnViewColorManagementIntentSaturation)
    ON_COMMAND(ID_VIEW_CM_INTENT_ABSOLUTECOLORIMETRIC, OnViewColorManagementIntentAbsoluteColorimetric)

    ON_COMMAND(ID_VIEW_EVROUTPUTRANGE_0_255, OnViewEVROutputRange_0_255)
    ON_COMMAND(ID_VIEW_EVROUTPUTRANGE_16_235, OnViewEVROutputRange_16_235)

    ON_COMMAND(ID_VIEW_FLUSHGPU_BEFOREVSYNC, OnViewFlushGPUBeforeVSync)
    ON_COMMAND(ID_VIEW_FLUSHGPU_AFTERPRESENT, OnViewFlushGPUAfterVSync)
    ON_COMMAND(ID_VIEW_FLUSHGPU_WAIT, OnViewFlushGPUWait)

    ON_COMMAND(ID_VIEW_D3DFULLSCREEN, OnViewD3DFullScreen)
    ON_COMMAND(ID_VIEW_DISABLEDESKTOPCOMPOSITION, OnViewDisableDesktopComposition)
    ON_COMMAND(ID_VIEW_ALTERNATIVEVSYNC, OnViewAlternativeVSync)
    ON_COMMAND(ID_VIEW_RESET_DEFAULT, OnViewResetDefault)

    ON_COMMAND(ID_VIEW_VSYNCOFFSET_INCREASE, OnViewVSyncOffsetIncrease)
    ON_COMMAND(ID_VIEW_VSYNCOFFSET_DECREASE, OnViewVSyncOffsetDecrease)
	ON_UPDATE_COMMAND_UI(ID_PRESIZE_SHADERS_TOGGLE, OnUpdateShaderToggle1)
	ON_COMMAND(ID_PRESIZE_SHADERS_TOGGLE, OnShaderToggle1)
	ON_UPDATE_COMMAND_UI(ID_POSTSIZE_SHADERS_TOGGLE, OnUpdateShaderToggle2)
	ON_COMMAND(ID_POSTSIZE_SHADERS_TOGGLE, OnShaderToggle2)
    ON_UPDATE_COMMAND_UI(ID_VIEW_OSD_DISPLAY_TIME, OnUpdateViewOSDDisplayTime)
    ON_COMMAND(ID_VIEW_OSD_DISPLAY_TIME, OnViewOSDDisplayTime)
    ON_UPDATE_COMMAND_UI(ID_VIEW_OSD_SHOW_FILENAME, OnUpdateViewOSDShowFileName)
    ON_COMMAND(ID_VIEW_OSD_SHOW_FILENAME, OnViewOSDShowFileName)
    ON_COMMAND(ID_D3DFULLSCREEN_TOGGLE, OnD3DFullscreenToggle)
    ON_COMMAND_RANGE(ID_GOTO_PREV_SUB, ID_GOTO_NEXT_SUB, OnGotoSubtitle)
    ON_COMMAND_RANGE(ID_SUBRESYNC_SHIFT_DOWN, ID_SUBRESYNC_SHIFT_UP, OnSubresyncShiftSub)
    ON_COMMAND_RANGE(ID_SUB_DELAY_DOWN, ID_SUB_DELAY_UP, OnSubtitleDelay)
    ON_COMMAND_RANGE(ID_SUB_POS_DOWN, ID_SUB_POS_UP, OnSubtitlePos)
    ON_COMMAND_RANGE(ID_SUB_FONT_SIZE_DEC, ID_SUB_FONT_SIZE_INC, OnSubtitleFontSize)

    ON_COMMAND(ID_PLAY_PLAY, OnPlayPlay)
    ON_COMMAND(ID_PLAY_PAUSE, OnPlayPause)
    ON_COMMAND(ID_PLAY_PLAYPAUSE, OnPlayPlaypause)
    ON_COMMAND(ID_PLAY_STOP, OnPlayStop)
    ON_UPDATE_COMMAND_UI(ID_PLAY_PLAY, OnUpdatePlayPauseStop)
    ON_UPDATE_COMMAND_UI(ID_PLAY_PAUSE, OnUpdatePlayPauseStop)
    ON_UPDATE_COMMAND_UI(ID_PLAY_PLAYPAUSE, OnUpdatePlayPauseStop)
    ON_UPDATE_COMMAND_UI(ID_PLAY_STOP, OnUpdatePlayPauseStop)
    ON_COMMAND_RANGE(ID_PLAY_FRAMESTEP, ID_PLAY_FRAMESTEP_BACK, OnPlayFramestep)
    ON_UPDATE_COMMAND_UI(ID_PLAY_FRAMESTEP, OnUpdatePlayFramestep)
    ON_COMMAND_RANGE(ID_PLAY_SEEKBACKWARDSMALL, ID_PLAY_SEEKFORWARDLARGE, OnPlaySeek)
    ON_COMMAND(ID_PLAY_SEEKSET, OnPlaySeekSet)
    ON_COMMAND_RANGE(ID_PLAY_SEEKKEYBACKWARD, ID_PLAY_SEEKKEYFORWARD, OnPlaySeekKey)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_SEEKBACKWARDSMALL, ID_PLAY_SEEKFORWARDLARGE, OnUpdatePlaySeek)
    ON_UPDATE_COMMAND_UI(ID_PLAY_SEEKSET, OnUpdatePlaySeek)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_SEEKKEYBACKWARD, ID_PLAY_SEEKKEYFORWARD, OnUpdatePlaySeek)
    ON_COMMAND_RANGE(ID_PLAY_DECRATE, ID_PLAY_INCRATE, OnPlayChangeRate)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_DECRATE, ID_PLAY_INCRATE, OnUpdatePlayChangeRate)
    ON_COMMAND_RANGE(ID_PLAY_PLAYBACKRATE_START, ID_PLAY_PLAYBACKRATE_END, OnPlayChangeRate)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_PLAYBACKRATE_START, ID_PLAY_PLAYBACKRATE_END, OnUpdatePlayChangeRate)
    ON_COMMAND(ID_PLAY_RESETRATE, OnPlayResetRate)
    ON_UPDATE_COMMAND_UI(ID_PLAY_RESETRATE, OnUpdatePlayResetRate)
    ON_COMMAND_RANGE(ID_PLAY_INCAUDDELAY, ID_PLAY_DECAUDDELAY, OnPlayChangeAudDelay)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_INCAUDDELAY, ID_PLAY_DECAUDDELAY, OnUpdatePlayChangeAudDelay)
    ON_COMMAND(ID_FILTERS_COPY_TO_CLIPBOARD, OnPlayFiltersCopyToClipboard)
    ON_COMMAND_RANGE(ID_FILTERS_SUBITEM_START, ID_FILTERS_SUBITEM_END, OnPlayFilters)
    ON_UPDATE_COMMAND_UI_RANGE(ID_FILTERS_SUBITEM_START, ID_FILTERS_SUBITEM_END, OnUpdatePlayFilters)
    ON_COMMAND(ID_SHADERS_SELECT, OnPlayShadersSelect)
    ON_COMMAND(ID_SHADERS_PRESET_NEXT, OnPlayShadersPresetNext)
    ON_COMMAND(ID_SHADERS_PRESET_PREV, OnPlayShadersPresetPrev)
    ON_COMMAND_RANGE(ID_SHADERS_PRESETS_START, ID_SHADERS_PRESETS_END, OnPlayShadersPresets)
    ON_COMMAND_RANGE(ID_AUDIO_SUBITEM_START, ID_AUDIO_SUBITEM_END, OnPlayAudio)
    ON_COMMAND_RANGE(ID_SUBTITLES_SUBITEM_START, ID_SUBTITLES_SUBITEM_END, OnPlaySubtitles)
    ON_COMMAND_RANGE(ID_SUBTITLES_SECONDARY_SUBITEM_START, ID_SUBTITLES_SECONDARY_SUBITEM_END, OnPlaySecondarySubtitle)
    ON_COMMAND(ID_SUBTITLES_SECONDARY_LOAD, OnSecondarySubtitleLoad)
    ON_COMMAND(ID_SUBTITLES_OVERRIDE_DEFAULT_STYLE, OnSubtitlesDefaultStyle)
    ON_COMMAND(ID_SUBTITLES_OVERRIDE_ALL_STYLES, OnSubtitlesOverrideStyles)
    ON_COMMAND_RANGE(ID_VIDEO_STREAMS_SUBITEM_START, ID_VIDEO_STREAMS_SUBITEM_END, OnPlayVideoStreams)
    ON_COMMAND_RANGE(ID_FILTERSTREAMS_SUBITEM_START, ID_FILTERSTREAMS_SUBITEM_END, OnPlayFiltersStreams)
    ON_COMMAND_RANGE(ID_VOLUME_UP, ID_VOLUME_MUTE, OnPlayVolume)
    ON_COMMAND_RANGE(ID_VOLUME_BOOST_INC, ID_VOLUME_BOOST_MAX, OnPlayVolumeBoost)
    ON_UPDATE_COMMAND_UI_RANGE(ID_VOLUME_BOOST_INC, ID_VOLUME_BOOST_MAX, OnUpdatePlayVolumeBoost)
    ON_COMMAND(ID_CUSTOM_CHANNEL_MAPPING, OnCustomChannelMapping)
    ON_UPDATE_COMMAND_UI(ID_CUSTOM_CHANNEL_MAPPING, OnUpdateCustomChannelMapping)
    ON_COMMAND_RANGE(ID_NORMALIZE, ID_REGAIN_VOLUME, OnNormalizeRegainVolume)
    ON_UPDATE_COMMAND_UI_RANGE(ID_NORMALIZE, ID_REGAIN_VOLUME, OnUpdateNormalizeRegainVolume)
    ON_COMMAND_RANGE(ID_COLOR_BRIGHTNESS_INC, ID_COLOR_RESET, OnPlayColor)
    ON_UPDATE_COMMAND_UI_RANGE(ID_AFTERPLAYBACK_EXIT, ID_AFTERPLAYBACK_MONITOROFF, OnUpdateAfterplayback)
    ON_COMMAND_RANGE(ID_AFTERPLAYBACK_EXIT, ID_AFTERPLAYBACK_MONITOROFF, OnAfterplayback)
    ON_UPDATE_COMMAND_UI_RANGE(ID_AFTERPLAYBACK_PLAYNEXT, ID_AFTERPLAYBACK_DONOTHING, OnUpdateAfterplayback)
    ON_COMMAND_RANGE(ID_AFTERPLAYBACK_PLAYNEXT, ID_AFTERPLAYBACK_DONOTHING, OnAfterplayback)
    ON_COMMAND_RANGE(ID_PLAY_REPEAT_ONEFILE, ID_PLAY_REPEAT_WHOLEPLAYLIST, OnPlayRepeat)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_REPEAT_ONEFILE, ID_PLAY_REPEAT_WHOLEPLAYLIST, OnUpdatePlayRepeat)
    ON_COMMAND_RANGE(ID_PLAY_REPEAT_AB, ID_PLAY_REPEAT_AB_MARK_B, OnABRepeat)
    ON_UPDATE_COMMAND_UI_RANGE(ID_PLAY_REPEAT_AB, ID_PLAY_REPEAT_AB_MARK_B, OnUpdateABRepeat)
    ON_COMMAND(ID_PLAY_REPEAT_FOREVER, OnPlayRepeatForever)
    ON_UPDATE_COMMAND_UI(ID_PLAY_REPEAT_FOREVER, OnUpdatePlayRepeatForever)

    ON_COMMAND_RANGE(ID_NAVIGATE_SKIPBACK, ID_NAVIGATE_SKIPFORWARD, OnNavigateSkip)
    ON_UPDATE_COMMAND_UI_RANGE(ID_NAVIGATE_SKIPBACK, ID_NAVIGATE_SKIPFORWARD, OnUpdateNavigateSkip)
    ON_COMMAND_RANGE(ID_NAVIGATE_SKIPBACKFILE, ID_NAVIGATE_SKIPFORWARDFILE, OnNavigateSkipFile)
    ON_UPDATE_COMMAND_UI_RANGE(ID_NAVIGATE_SKIPBACKFILE, ID_NAVIGATE_SKIPFORWARDFILE, OnUpdateNavigateSkipFile)
    ON_COMMAND(ID_NAVIGATE_GOTO, OnNavigateGoto)
    ON_UPDATE_COMMAND_UI(ID_NAVIGATE_GOTO, OnUpdateNavigateGoto)
    ON_COMMAND_RANGE(ID_NAVIGATE_TITLEMENU, ID_NAVIGATE_CHAPTERMENU, OnNavigateMenu)
    ON_UPDATE_COMMAND_UI_RANGE(ID_NAVIGATE_TITLEMENU, ID_NAVIGATE_CHAPTERMENU, OnUpdateNavigateMenu)
    ON_COMMAND_RANGE(ID_NAVIGATE_JUMPTO_SUBITEM_START, ID_NAVIGATE_JUMPTO_SUBITEM_END, OnNavigateJumpTo)
    ON_COMMAND_RANGE(ID_NAVIGATE_MENU_LEFT, ID_NAVIGATE_MENU_LEAVE, OnNavigateMenuItem)
    ON_UPDATE_COMMAND_UI_RANGE(ID_NAVIGATE_MENU_LEFT, ID_NAVIGATE_MENU_LEAVE, OnUpdateNavigateMenuItem)

    ON_COMMAND(ID_NAVIGATE_TUNERSCAN, OnTunerScan)
    ON_UPDATE_COMMAND_UI(ID_NAVIGATE_TUNERSCAN, OnUpdateTunerScan)

    ON_COMMAND(ID_FAVORITES_ADD, OnFavoritesAdd)
    ON_UPDATE_COMMAND_UI(ID_FAVORITES_ADD, OnUpdateFavoritesAdd)
    ON_COMMAND(ID_FAVORITES_QUICKADDFAVORITE, OnFavoritesQuickAddFavorite)
    ON_COMMAND(ID_FAVORITES_ORGANIZE, OnFavoritesOrganize)
    ON_UPDATE_COMMAND_UI(ID_FAVORITES_ORGANIZE, OnUpdateFavoritesOrganize)
    ON_COMMAND_RANGE(ID_FAVORITES_FILE_START, ID_FAVORITES_FILE_END, OnFavoritesFile)
    ON_UPDATE_COMMAND_UI_RANGE(ID_FAVORITES_FILE_START, ID_FAVORITES_FILE_END, OnUpdateFavoritesFile)
    ON_COMMAND_RANGE(ID_FAVORITES_DVD_START, ID_FAVORITES_DVD_END, OnFavoritesDVD)
    ON_UPDATE_COMMAND_UI_RANGE(ID_FAVORITES_DVD_START, ID_FAVORITES_DVD_END, OnUpdateFavoritesDVD)
    ON_COMMAND_RANGE(ID_FAVORITES_DEVICE_START, ID_FAVORITES_DEVICE_END, OnFavoritesDevice)
    ON_UPDATE_COMMAND_UI_RANGE(ID_FAVORITES_DEVICE_START, ID_FAVORITES_DEVICE_END, OnUpdateFavoritesDevice)

    ON_COMMAND(ID_RECENT_FILES_CLEAR, OnRecentFileClear)
    ON_UPDATE_COMMAND_UI(ID_RECENT_FILES_CLEAR, OnUpdateRecentFileClear)
    ON_COMMAND_RANGE(ID_RECENT_FILE_START, ID_RECENT_FILE_END, OnRecentFile)
    ON_UPDATE_COMMAND_UI_RANGE(ID_RECENT_FILE_START, ID_RECENT_FILE_END, OnUpdateRecentFile)
    ON_COMMAND(ID_RECENT_FILES_SHOW_HISTORY, OnShowHistory)

    ON_COMMAND(ID_HELP_HOMEPAGE, OnHelpHomepage)
    ON_COMMAND(ID_HELP_CHECKFORUPDATE, OnHelpCheckForUpdate)
    ON_COMMAND(ID_HELP_TOOLBARIMAGES, OnHelpToolbarImages)
    ON_COMMAND(ID_HELP_DONATE, OnHelpDonate)

    // Open Dir incl. SubDir
    ON_COMMAND(ID_FILE_OPENDIRECTORY, OnFileOpendirectory)
    ON_UPDATE_COMMAND_UI(ID_FILE_OPENDIRECTORY, OnUpdateFileOpen)
    ON_WM_POWERBROADCAST()

    // Support toolbar dropdown buttons
    ON_UPDATE_COMMAND_UI(ID_AUDIOS, OnUpdateAudiosButton)
    ON_UPDATE_COMMAND_UI(ID_SUBTITLES, OnUpdateSubtitlesButton)

    // Navigation panel
    ON_COMMAND(ID_VIEW_NAVIGATION, OnViewNavigation)
    ON_UPDATE_COMMAND_UI(ID_VIEW_NAVIGATION, OnUpdateViewNavigation)

    ON_WM_WTSSESSION_CHANGE()

    ON_MESSAGE(WM_LOADSUBTITLES, OnLoadSubtitles)
    ON_MESSAGE(WM_GETSUBTITLES, OnGetSubtitles)
    ON_WM_DRAWITEM()
    ON_WM_SETTINGCHANGE()
    ON_WM_MOUSEHWHEEL()
END_MESSAGE_MAP()

//#ifdef _DEBUG
const TCHAR* GetEventString(LONG evCode)
{
#define UNPACK_VALUE(VALUE) case VALUE: return _T(#VALUE);
    switch (evCode) {
            // System-defined event codes
            UNPACK_VALUE(EC_COMPLETE);
            UNPACK_VALUE(EC_USERABORT);
            UNPACK_VALUE(EC_ERRORABORT);
            //UNPACK_VALUE(EC_TIME);
            UNPACK_VALUE(EC_REPAINT);
            UNPACK_VALUE(EC_STREAM_ERROR_STOPPED);
            UNPACK_VALUE(EC_STREAM_ERROR_STILLPLAYING);
            UNPACK_VALUE(EC_ERROR_STILLPLAYING);
            UNPACK_VALUE(EC_PALETTE_CHANGED);
            UNPACK_VALUE(EC_VIDEO_SIZE_CHANGED);
            UNPACK_VALUE(EC_QUALITY_CHANGE);
            UNPACK_VALUE(EC_SHUTTING_DOWN);
            UNPACK_VALUE(EC_CLOCK_CHANGED);
            UNPACK_VALUE(EC_PAUSED);
            UNPACK_VALUE(EC_OPENING_FILE);
            UNPACK_VALUE(EC_BUFFERING_DATA);
            UNPACK_VALUE(EC_FULLSCREEN_LOST);
            UNPACK_VALUE(EC_ACTIVATE);
            UNPACK_VALUE(EC_NEED_RESTART);
            UNPACK_VALUE(EC_WINDOW_DESTROYED);
            UNPACK_VALUE(EC_DISPLAY_CHANGED);
            UNPACK_VALUE(EC_STARVATION);
            UNPACK_VALUE(EC_OLE_EVENT);
            UNPACK_VALUE(EC_NOTIFY_WINDOW);
            UNPACK_VALUE(EC_STREAM_CONTROL_STOPPED);
            UNPACK_VALUE(EC_STREAM_CONTROL_STARTED);
            UNPACK_VALUE(EC_END_OF_SEGMENT);
            UNPACK_VALUE(EC_SEGMENT_STARTED);
            UNPACK_VALUE(EC_LENGTH_CHANGED);
            UNPACK_VALUE(EC_DEVICE_LOST);
            UNPACK_VALUE(EC_SAMPLE_NEEDED);
            UNPACK_VALUE(EC_PROCESSING_LATENCY);
            UNPACK_VALUE(EC_SAMPLE_LATENCY);
            UNPACK_VALUE(EC_SCRUB_TIME);
            UNPACK_VALUE(EC_STEP_COMPLETE);
            UNPACK_VALUE(EC_TIMECODE_AVAILABLE);
            UNPACK_VALUE(EC_EXTDEVICE_MODE_CHANGE);
            UNPACK_VALUE(EC_STATE_CHANGE);
            UNPACK_VALUE(EC_GRAPH_CHANGED);
            UNPACK_VALUE(EC_CLOCK_UNSET);
            UNPACK_VALUE(EC_VMR_RENDERDEVICE_SET);
            UNPACK_VALUE(EC_VMR_SURFACE_FLIPPED);
            UNPACK_VALUE(EC_VMR_RECONNECTION_FAILED);
            UNPACK_VALUE(EC_PREPROCESS_COMPLETE);
            UNPACK_VALUE(EC_CODECAPI_EVENT);
            UNPACK_VALUE(EC_WMT_INDEX_EVENT);
            UNPACK_VALUE(EC_WMT_EVENT);
            UNPACK_VALUE(EC_BUILT);
            UNPACK_VALUE(EC_UNBUILT);
            UNPACK_VALUE(EC_SKIP_FRAMES);
            UNPACK_VALUE(EC_PLEASE_REOPEN);
            UNPACK_VALUE(EC_STATUS);
            UNPACK_VALUE(EC_MARKER_HIT);
            UNPACK_VALUE(EC_LOADSTATUS);
            UNPACK_VALUE(EC_FILE_CLOSED);
            UNPACK_VALUE(EC_ERRORABORTEX);
            //UNPACK_VALUE(EC_NEW_PIN);
            //UNPACK_VALUE(EC_RENDER_FINISHED);
            UNPACK_VALUE(EC_EOS_SOON);
            UNPACK_VALUE(EC_CONTENTPROPERTY_CHANGED);
            UNPACK_VALUE(EC_BANDWIDTHCHANGE);
            UNPACK_VALUE(EC_VIDEOFRAMEREADY);
            // DVD-Video event codes
            UNPACK_VALUE(EC_DVD_DOMAIN_CHANGE);
            UNPACK_VALUE(EC_DVD_TITLE_CHANGE);
            UNPACK_VALUE(EC_DVD_CHAPTER_START);
            UNPACK_VALUE(EC_DVD_AUDIO_STREAM_CHANGE);
            UNPACK_VALUE(EC_DVD_SUBPICTURE_STREAM_CHANGE);
            UNPACK_VALUE(EC_DVD_ANGLE_CHANGE);
            UNPACK_VALUE(EC_DVD_BUTTON_CHANGE);
            UNPACK_VALUE(EC_DVD_VALID_UOPS_CHANGE);
            UNPACK_VALUE(EC_DVD_STILL_ON);
            UNPACK_VALUE(EC_DVD_STILL_OFF);
            UNPACK_VALUE(EC_DVD_CURRENT_TIME);
            UNPACK_VALUE(EC_DVD_ERROR);
            UNPACK_VALUE(EC_DVD_WARNING);
            UNPACK_VALUE(EC_DVD_CHAPTER_AUTOSTOP);
            UNPACK_VALUE(EC_DVD_NO_FP_PGC);
            UNPACK_VALUE(EC_DVD_PLAYBACK_RATE_CHANGE);
            UNPACK_VALUE(EC_DVD_PARENTAL_LEVEL_CHANGE);
            UNPACK_VALUE(EC_DVD_PLAYBACK_STOPPED);
            UNPACK_VALUE(EC_DVD_ANGLES_AVAILABLE);
            UNPACK_VALUE(EC_DVD_PLAYPERIOD_AUTOSTOP);
            UNPACK_VALUE(EC_DVD_BUTTON_AUTO_ACTIVATED);
            UNPACK_VALUE(EC_DVD_CMD_START);
            UNPACK_VALUE(EC_DVD_CMD_END);
            UNPACK_VALUE(EC_DVD_DISC_EJECTED);
            UNPACK_VALUE(EC_DVD_DISC_INSERTED);
            UNPACK_VALUE(EC_DVD_CURRENT_HMSF_TIME);
            UNPACK_VALUE(EC_DVD_KARAOKE_MODE);
            UNPACK_VALUE(EC_DVD_PROGRAM_CELL_CHANGE);
            UNPACK_VALUE(EC_DVD_TITLE_SET_CHANGE);
            UNPACK_VALUE(EC_DVD_PROGRAM_CHAIN_CHANGE);
            UNPACK_VALUE(EC_DVD_VOBU_Offset);
            UNPACK_VALUE(EC_DVD_VOBU_Timestamp);
            UNPACK_VALUE(EC_DVD_GPRM_Change);
            UNPACK_VALUE(EC_DVD_SPRM_Change);
            UNPACK_VALUE(EC_DVD_BeginNavigationCommands);
            UNPACK_VALUE(EC_DVD_NavigationCommand);
            // Sound device error event codes
            UNPACK_VALUE(EC_SNDDEV_IN_ERROR);
            UNPACK_VALUE(EC_SNDDEV_OUT_ERROR);
            // Custom event codes
            UNPACK_VALUE(EC_BG_AUDIO_CHANGED);
            UNPACK_VALUE(EC_BG_ERROR);
    };
#undef UNPACK_VALUE
    CString ret;
    ret.Format(_T("UNKNOWN 0x%08x"), evCode);
    return ret;
}
//#endif

void CMainFrame::EventCallback(MpcEvent ev)
{
    const auto& s = AfxGetAppSettings();
    switch (ev) {
        case MpcEvent::SHADER_SELECTION_CHANGED:
        case MpcEvent::SHADER_PRERESIZE_SELECTION_CHANGED:
        case MpcEvent::SHADER_POSTRESIZE_SELECTION_CHANGED:
            SetShaders(m_bToggleShader, m_bToggleShaderScreenSpace);
            break;
        case MpcEvent::DISPLAY_MODE_AUTOCHANGING:
            if (GetLoadState() == MLS::LOADED && GetMediaState() == State_Running && s.autoChangeFSMode.uDelay) {
                // pause if the mode is being changed during playback
                OnPlayPause();
                m_bPausedForAutochangeMonitorMode = true;
            }
            break;
        case MpcEvent::DISPLAY_MODE_AUTOCHANGED:
            if (GetLoadState() == MLS::LOADED) {
                if (m_bPausedForAutochangeMonitorMode && s.autoChangeFSMode.uDelay) {
                    // delay play if was paused due to mode change
                    ASSERT(GetMediaState() != State_Stopped);
                    const unsigned uModeChangeDelay = s.autoChangeFSMode.uDelay * 1000;
                    m_timerOneTime.Subscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE,
                                             std::bind(&CMainFrame::OnPlayPlay, this), uModeChangeDelay);
                } else if (m_bDelaySetOutputRect) {
                    ASSERT(GetMediaState() == State_Stopped);
                    // tell OnFilePostOpenmedia() to delay entering play or paused state
                    m_bOpeningInAutochangedMonitorMode = true;
                }
            }
            break;
        case MpcEvent::CHANGING_UI_LANGUAGE:
            UpdateUILanguage();
            break;
        case MpcEvent::STREAM_POS_UPDATE_REQUEST:
            OnTimer(TIMER_STREAMPOSPOLLER);
            OnTimer(TIMER_STREAMPOSPOLLER2);
            break;
        default:
            ASSERT(FALSE);
    }
}

/////////////////////////////////////////////////////////////////////////////
// CMainFrame construction/destruction

CMainFrame::CMainFrame()
    : m_timerHider(this, TIMER_HIDER, 200)
    , m_timerOneTime(this, TIMER_ONETIME_START, TIMER_ONETIME_END - TIMER_ONETIME_START + 1)
    , m_bUsingDXVA(false)
    , m_HWAccelType(nullptr)
    , m_posFirstExtSub(nullptr)
    , m_bDelaySetOutputRect(false)
    , m_nJumpToSubMenusCount(0)
    , m_nLoops(0)
    , m_nLastSkipDirection(0)
    , m_fCustomGraph(false)
    , m_fShockwaveGraph(false)
    , m_fFrameSteppingActive(false)
    , m_nStepForwardCount(0)
    , m_rtStepForwardStart(0)
    , m_nVolumeBeforeFrameStepping(0)
    , m_fEndOfStream(false)
    , m_dwLastPause(0ULL)
    , m_reloadFilename(L"")
    , m_rtReloadPos(-1)
    , m_iReloadAudioIdx(-1)
    , m_iReloadSubIdx(-1)
    , m_bRememberFilePos(false)
    , m_dwLastRun(0)
    , m_nLastAppendSelectionIndex(0)
    , m_bBuffering(false)
    , m_fLiveWM(false)
    , m_rtDurationOverride(-1)
    , m_iPlaybackMode(PM_NONE)
    , m_lCurrentChapter(0)
    , m_lChapterStartTime(0xFFFFFFFF)
    , m_eMediaLoadState(MLS::CLOSED)
    , m_CachedFilterState(-1)
    , m_bSettingUpMenus(false)
    , m_bOpenMediaActive(false)
    , m_OpenMediaFailedCount(0)
    , m_fFullScreen(false)
    , m_bFullScreenWindowIsD3D(false)
    , m_bFullScreenWindowIsOnSeparateDisplay(false)
    , m_bNeedZoomAfterFullscreenExit(false)
    , m_fStartInD3DFullscreen(false)
    , m_fStartInFullscreenSeparate(false)
    , m_pLastBar(nullptr)
    , m_bFirstPlay(false)
    , m_bOpeningInAutochangedMonitorMode(false)
    , m_bPausedForAutochangeMonitorMode(false)
    , m_fAudioOnly(true)
    , m_iDVDDomain(DVD_DOMAIN_Stop)
    , m_iDVDTitle(0)
    , m_bDVDStillOn(false)
    , m_dSpeedRate(1.0)
    , m_ZoomX(1.0)
    , m_ZoomY(1.0)
    , m_PosX(0.5)
    , m_PosY(0.5)
    , m_AngleX(0)
    , m_AngleY(0)
    , m_AngleZ(0)
    , m_iDefRotation(0)
    , m_pGraphThread(nullptr)
    , m_bOpenedThroughThread(false)
    , m_evOpenPrivateFinished(FALSE, TRUE)
    , m_evClosePrivateFinished(FALSE, TRUE)
    , m_fOpeningAborted(false)
    , m_bWasSnapped(false)
    , m_wndSubtitlesDownloadDialog(this)
    //, m_wndSubtitlesUploadDialog(this)
    , m_wndFavoriteOrganizeDialog(this)
    , m_bTrayIcon(false)
    , m_fCapturing(false)
    , m_controls(this)
    , m_wndView(this)
    , m_wndSeekBar(this)
    , m_wndToolBar(this)
    , m_wndInfoBar(this)
    , m_wndStatsBar(this)
    , m_wndStatusBar(this)
    , m_wndSubresyncBar(this)
    , m_wndPlaylistBar(this)
    , m_wndPreView(this)
    , m_wndCaptureBar(this)
    , m_wndNavigationBar(this)
    , m_pVideoWnd(nullptr)
    , m_pOSDWnd(nullptr)
    , m_pDedicatedFSVideoWnd(nullptr)
    , m_OSD(this)
    , m_nCurSubtitle(-1)
    , m_lSubtitleShift(0)
    , m_rtCurSubPos(0)
    , m_nLastCopiedSubSegment(-1)
    , m_rtNextAutoCopySubtitle(0)
    , m_bScanDlgOpened(false)
    , m_bStopTunerScan(false)
    , m_bLockedZoomVideoWindow(false)
    , m_nLockedZoomVideoWindow(0)
    , m_pActiveContextMenu(nullptr)
    , m_pActiveSystemMenu(nullptr)
    , m_bAltDownClean(false)
    , m_bShowingFloatingMenubar(false)
    , m_bAllowWindowZoom(false)
    , m_dLastVideoScaleFactor(0)
    , m_bExtOnTop(false)
    , m_bIsBDPlay(false)
    , m_bHasBDMeta(false)
    , watchingDialog(themableDialogTypes::None)
    , dialogHookHelper(nullptr)
    , delayingFullScreen(false)
    , restoringWindowRect(false)
    , mediaTypesErrorDlg(nullptr)
    , m_iStreamPosPollerInterval(100)
    , currentAudioLang(_T(""))
    , currentSubLang(_T(""))
    , m_bToggleShader(false)
    , m_bToggleShaderScreenSpace(false)
    , m_MPLSPlaylist()
    , m_sydlLastProcessURL()
    , m_bUseSeekPreview(false)
    , queuedSeek({0,0,false})
    , lastSeekStart(0)
    , lastSeekFinish(0)
    , defaultVideoAngle(0)
    , m_media_trans_control()
    , recentFilesMenuFromMRUSequence(-1)
    , m_bTBDropdownActive(false)
{
    // Don't let CFrameWnd handle automatically the state of the menu items.
    // This means that menu items without handlers won't be automatically
    // disabled but it avoids some unwanted cases where programmatically
    // disabled menu items are always re-enabled by CFrameWnd.
    m_bAutoMenuEnable = FALSE;

    EventRouter::EventSelection receives;
    receives.insert(MpcEvent::SHADER_SELECTION_CHANGED);
    receives.insert(MpcEvent::SHADER_PRERESIZE_SELECTION_CHANGED);
    receives.insert(MpcEvent::SHADER_POSTRESIZE_SELECTION_CHANGED);
    receives.insert(MpcEvent::DISPLAY_MODE_AUTOCHANGING);
    receives.insert(MpcEvent::DISPLAY_MODE_AUTOCHANGED);
    receives.insert(MpcEvent::CHANGING_UI_LANGUAGE);
    receives.insert(MpcEvent::STREAM_POS_UPDATE_REQUEST);
    EventRouter::EventSelection fires;
    fires.insert(MpcEvent::SWITCHING_TO_FULLSCREEN);
    fires.insert(MpcEvent::SWITCHED_TO_FULLSCREEN);
    fires.insert(MpcEvent::SWITCHING_FROM_FULLSCREEN);
    fires.insert(MpcEvent::SWITCHED_FROM_FULLSCREEN);
    fires.insert(MpcEvent::SWITCHING_TO_FULLSCREEN_D3D);
    fires.insert(MpcEvent::SWITCHED_TO_FULLSCREEN_D3D);
    fires.insert(MpcEvent::MEDIA_LOADED);
    fires.insert(MpcEvent::DISPLAY_MODE_AUTOCHANGING);
    fires.insert(MpcEvent::DISPLAY_MODE_AUTOCHANGED);
    fires.insert(MpcEvent::CONTEXT_MENU_POPUP_INITIALIZED);
    fires.insert(MpcEvent::CONTEXT_MENU_POPUP_UNINITIALIZED);
    fires.insert(MpcEvent::SYSTEM_MENU_POPUP_INITIALIZED);
    fires.insert(MpcEvent::SYSTEM_MENU_POPUP_UNINITIALIZED);
    fires.insert(MpcEvent::DPI_CHANGED);
    GetEventd().Connect(m_eventc, receives, std::bind(&CMainFrame::EventCallback, this, std::placeholders::_1), fires);
}

CMainFrame::~CMainFrame()
{
    if (defaultMPCThemeMenu != nullptr) {
        delete defaultMPCThemeMenu;
    }
}

int CMainFrame::OnNcCreate(LPCREATESTRUCT lpCreateStruct)
{
    if (IsWindows10OrGreater()) {
        // Tell Windows to automatically handle scaling of non-client areas
        // such as the caption bar. EnableNonClientDpiScaling was introduced in Windows 10
        const WinapiFunc<BOOL WINAPI(HWND)>
        fnEnableNonClientDpiScaling = { _T("User32.dll"), "EnableNonClientDpiScaling" };

        if (fnEnableNonClientDpiScaling) {
            fnEnableNonClientDpiScaling(m_hWnd);
        }
    }

    return __super::OnNcCreate(lpCreateStruct);
}

int CMainFrame::OnCreate(LPCREATESTRUCT lpCreateStruct)
{
    if (__super::OnCreate(lpCreateStruct) == -1) {
        return -1;
    }

    CMPCThemeUtil::enableWindows10DarkFrame(this);

    if (IsWindows8Point1OrGreater()) {
        m_dpi.Override(m_hWnd);
    }

    const WinapiFunc<decltype(ChangeWindowMessageFilterEx)>
    fnChangeWindowMessageFilterEx = { _T("user32.dll"), "ChangeWindowMessageFilterEx" };

    // allow taskbar messages through UIPI
    if (fnChangeWindowMessageFilterEx) {
        VERIFY(fnChangeWindowMessageFilterEx(m_hWnd, s_uTaskbarRestart, MSGFLT_ALLOW, nullptr));
        VERIFY(fnChangeWindowMessageFilterEx(m_hWnd, s_uTBBC, MSGFLT_ALLOW, nullptr));
        VERIFY(fnChangeWindowMessageFilterEx(m_hWnd, WM_COMMAND, MSGFLT_ALLOW, nullptr));
    }

    VERIFY(m_popupMenu.LoadMenu(IDR_POPUP));
    VERIFY(m_mainPopupMenu.LoadMenu(IDR_POPUPMAIN));
    CreateDynamicMenus();

    // create a view to occupy the client area of the frame
    if (!m_wndView.Create(nullptr, nullptr, AFX_WS_DEFAULT_VIEW,
                          CRect(0, 0, 0, 0), this, AFX_IDW_PANE_FIRST, nullptr)) {
        TRACE(_T("Failed to create view window\n"));
        return -1;
    }
    // Should never be RTLed
    m_wndView.ModifyStyleEx(WS_EX_LAYOUTRTL, WS_EX_NOINHERITLAYOUT);

    const CAppSettings& s = AfxGetAppSettings();

    // Create OSD Window
    CreateOSDBar();

    // Create Preview Window
    if (s.fSeekPreview) {
        if (m_wndPreView.CreateEx(0, AfxRegisterWndClass(0), nullptr, WS_POPUP | WS_CLIPCHILDREN | WS_CLIPSIBLINGS, CRect(0, 0, 160, 109), this, 0)) {
            m_wndPreView.ShowWindow(SW_HIDE);
            m_wndPreView.SetRelativeSize(AfxGetAppSettings().iSeekPreviewSize);
        } else {
            TRACE(_T("Failed to create Preview Window"));
        }
    }

    // static bars

    BOOL bResult = m_wndStatusBar.Create(this);
    if (bResult) {
        bResult = m_wndStatsBar.Create(this);
    }
    if (bResult) {
        bResult = m_wndInfoBar.Create(this);
    }
    if (bResult) {
        bResult = m_wndToolBar.Create(this);
    }
    if (bResult) {
        m_wndToolBar.GetToolBarCtrl().HideButton(ID_PLAY_PAUSE);

        bResult = m_wndSeekBar.Create(this);
    }
    if (!bResult) {
        TRACE(_T("Failed to create all control bars\n"));
        return -1;      // fail to create
    }

    m_pDedicatedFSVideoWnd = DEBUG_NEW CFullscreenWnd(this);

    m_controls.m_toolbars[CMainFrameControls::Toolbar::SEEKBAR] = &m_wndSeekBar;
    m_controls.m_toolbars[CMainFrameControls::Toolbar::CONTROLS] = &m_wndToolBar;
    m_controls.m_toolbars[CMainFrameControls::Toolbar::INFO] = &m_wndInfoBar;
    m_controls.m_toolbars[CMainFrameControls::Toolbar::STATS] = &m_wndStatsBar;
    m_controls.m_toolbars[CMainFrameControls::Toolbar::STATUS] = &m_wndStatusBar;

    // dockable bars

    EnableDocking(CBRS_ALIGN_ANY);

    bResult = m_wndSubresyncBar.Create(this, AFX_IDW_DOCKBAR_TOP, &m_csSubLock);
    if (bResult) {
        m_wndSubresyncBar.SetBarStyle(m_wndSubresyncBar.GetBarStyle() | CBRS_TOOLTIPS | CBRS_FLYBY | CBRS_SIZE_DYNAMIC);
        m_wndSubresyncBar.EnableDocking(CBRS_ALIGN_ANY);
        m_wndSubresyncBar.SetHeight(200);
        m_controls.m_panels[CMainFrameControls::Panel::SUBRESYNC] = &m_wndSubresyncBar;
    }
    bResult = bResult && m_wndPlaylistBar.Create(this, AFX_IDW_DOCKBAR_RIGHT);
    if (bResult) {
        m_wndPlaylistBar.SetBarStyle(m_wndPlaylistBar.GetBarStyle() | CBRS_TOOLTIPS | CBRS_FLYBY | CBRS_SIZE_DYNAMIC);
        m_wndPlaylistBar.EnableDocking(CBRS_ALIGN_ANY);
        m_wndPlaylistBar.SetWidth(300);
        m_controls.m_panels[CMainFrameControls::Panel::PLAYLIST] = &m_wndPlaylistBar;
        //m_wndPlaylistBar.LoadPlaylist(GetRecentFile()); //adipose 2019-11-12; do this later after activating the frame
    }
    bResult = bResult && m_wndEditListEditor.Create(this, AFX_IDW_DOCKBAR_RIGHT);
    if (bResult) {
        m_wndEditListEditor.SetBarStyle(m_wndEditListEditor.GetBarStyle() | CBRS_TOOLTIPS | CBRS_FLYBY | CBRS_SIZE_DYNAMIC);
        m_wndEditListEditor.EnableDocking(CBRS_ALIGN_ANY);
        m_controls.m_panels[CMainFrameControls::Panel::EDL] = &m_wndEditListEditor;
        m_wndEditListEditor.SetHeight(100);
    }
    bResult = bResult && m_wndCaptureBar.Create(this, AFX_IDW_DOCKBAR_LEFT);
    if (bResult) {
        m_wndCaptureBar.SetBarStyle(m_wndCaptureBar.GetBarStyle() | CBRS_TOOLTIPS | CBRS_FLYBY | CBRS_SIZE_DYNAMIC);
        m_wndCaptureBar.EnableDocking(CBRS_ALIGN_LEFT | CBRS_ALIGN_RIGHT);
        m_controls.m_panels[CMainFrameControls::Panel::CAPTURE] = &m_wndCaptureBar;
    }
    bResult = bResult && m_wndNavigationBar.Create(this, AFX_IDW_DOCKBAR_LEFT);
    if (bResult) {
        m_wndNavigationBar.SetBarStyle(m_wndNavigationBar.GetBarStyle() | CBRS_TOOLTIPS | CBRS_FLYBY | CBRS_SIZE_DYNAMIC);
        m_wndNavigationBar.EnableDocking(CBRS_ALIGN_LEFT | CBRS_ALIGN_RIGHT);
        m_controls.m_panels[CMainFrameControls::Panel::NAVIGATION] = &m_wndNavigationBar;
    }
    if (!bResult) {
        TRACE(_T("Failed to create all dockable bars\n"));
        return -1;
    }

    // Hide all controls initially
    for (const auto& pair : m_controls.m_toolbars) {
        pair.second->ShowWindow(SW_HIDE);
    }
    for (const auto& pair : m_controls.m_panels) {
        pair.second->ShowWindow(SW_HIDE);
    }

    m_dropTarget.Register(this);

    SetAlwaysOnTop(s.iOnTop);

    ShowTrayIcon(s.fTrayIcon);

    m_Lcd.SetVolumeRange(0, 100);
    m_Lcd.SetVolume(std::max(1, s.nVolume));

    m_pGraphThread = (CGraphThread*)AfxBeginThread(RUNTIME_CLASS(CGraphThread));
    if (m_pGraphThread) {
        m_pGraphThread->SetMainFrame(this);
    }

    m_pSubtitlesProviders = std::make_unique<SubtitlesProviders>(this);
    m_wndSubtitlesDownloadDialog.Create(m_wndSubtitlesDownloadDialog.IDD, this);
    //m_wndSubtitlesUploadDialog.Create(m_wndSubtitlesUploadDialog.IDD, this);
    m_wndFavoriteOrganizeDialog.Create(m_wndFavoriteOrganizeDialog.IDD, this);

    if (s.nCmdlnWebServerPort != 0) {
        if (s.nCmdlnWebServerPort > 0) {
            StartWebServer(s.nCmdlnWebServerPort);
        } else if (s.fEnableWebServer) {
            StartWebServer(s.nWebServerPort);
        }
    }

    m_bToggleShader = s.bToggleShader;
    m_bToggleShaderScreenSpace = s.bToggleShaderScreenSpace;
    OpenSetupWindowTitle(true);

    WTSRegisterSessionNotification();

    m_popupMenu.fulfillThemeReqs();
    m_mainPopupMenu.fulfillThemeReqs();

    if (s.bUseSMTC) {
        m_media_trans_control.Init(this);
    }

    if (m_wndTabletFrame.Create(this)) {
        m_wndTabletFrame.SyncToOwner();
    }

    return 0;
}

void CMainFrame::CreateOSDBar() {
    if (SUCCEEDED(m_OSD.Create(&m_wndView))) {
        m_pOSDWnd = &m_wndView;
    }
}

bool CMainFrame::OSDBarSetPos() {
    if (!m_OSD || !(::IsWindow(m_OSD.GetSafeHwnd())) || m_OSD.GetOSDType() != OSD_TYPE_GDI) {
        return false;
    }
    const CAppSettings& s = AfxGetAppSettings();

    if (s.iDSVideoRendererType == VIDRNDT_DS_MADVR || !m_wndView.IsWindowVisible()) {
        if (m_OSD.IsWindowVisible()) {
            m_OSD.ShowWindow(SW_HIDE);
        }
        return false;
    }

    CRect r_wndView;
    m_wndView.GetWindowRect(&r_wndView);

    int pos = 0;

    CRect MainWndRect;
    m_wndView.GetWindowRect(&MainWndRect);
    MainWndRect.right -= pos;
    m_OSD.SetWndRect(MainWndRect);
    if (m_OSD.IsWindowVisible()) {
        ::PostMessageW(m_OSD.m_hWnd, WM_OSD_DRAW, WPARAM(0), LPARAM(0));
    }

    return false;
}

void CMainFrame::DestroyOSDBar() {
    if (m_OSD) {
        m_OSD.Stop();
        m_OSD.DestroyWindow();
    }
}

void CMainFrame::OnMeasureItem(int nIDCtl, LPMEASUREITEMSTRUCT lpMeasureItemStruct)
{
    if (lpMeasureItemStruct->CtlType == ODT_MENU)  {
        if (CMPCThemeMenu* cm = CMPCThemeMenu::getParentMenu(lpMeasureItemStruct->itemID)) {
            cm->MeasureItem(lpMeasureItemStruct);
            return;
        }
    }

    CFrameWnd::OnMeasureItem(nIDCtl, lpMeasureItemStruct);
}


LRESULT CMainFrame::OnLAVPropPageCallback(WPARAM, LPARAM lParam)
{
    CComPtr<IBaseFilter> pBF;
    pBF.Attach(reinterpret_cast<IBaseFilter*>(lParam)); // takes the AddRef from PostMessage
    if (pBF && !m_bLAVPropPageOpen) {
        m_bLAVPropPageOpen = true;
        CFGFilterLAV::PropertyPageCallback(pBF);
        m_bLAVPropPageOpen = false;
    }
    return 0;
}

void CMainFrame::OnDestroy()
{
    if (::IsWindow(m_wndTabletFrame.GetSafeHwnd())) {
        m_wndTabletFrame.DestroyWindow();
    }

    WTSUnRegisterSessionNotification();
    ShowTrayIcon(false);
    m_dropTarget.Revoke();

    if (m_pDebugShaders && IsWindow(m_pDebugShaders->m_hWnd)) {
        VERIFY(m_pDebugShaders->DestroyWindow());
    }

    if (m_pColorControls && IsWindow(m_pColorControls->m_hWnd)) {
        VERIFY(m_pColorControls->DestroyWindow());
    }

    if (m_pHistoryDlg && IsWindow(m_pHistoryDlg->m_hWnd)) {
        VERIFY(m_pHistoryDlg->DestroyWindow());
    }

    if (m_pGraphThread && m_pGraphThread->m_hThread) {
        CAMMsgEvent e;
        if (!m_pGraphThread->PostThreadMessage(CGraphThread::TM_EXIT, (WPARAM)0, (LPARAM)&e) || !e.Wait(2000)) {
            PLAYER_LOG(_T("CMainFrame::OnDestroy - Terminating graph thread due to timeout or failure"));
            FLUSH_LOGGER();
            TerminateThread(m_pGraphThread->m_hThread, DWORD_ERROR);
            ASSERT(false);
        }
    }

    if (m_pDedicatedFSVideoWnd) {
        if (m_pDedicatedFSVideoWnd->IsWindow()) {
            m_pDedicatedFSVideoWnd->DestroyWindow();
        }
        delete m_pDedicatedFSVideoWnd;
    }

    m_wndPreView.DestroyWindow();

    __super::OnDestroy();
}

void CMainFrame::OnClose()
{
    CAppSettings& s = AfxGetAppSettings();

    m_OnClose_called = true;

    if (USE_LOGGER(s)) {
        PLAYER_LOG(_T("CMainFrame::OnClose"));
        FLUSH_LOGGER();
    }

    ASSERT(GetCurrentThreadId() == AfxGetApp()->m_nThreadID);

    s.bToggleShader = m_bToggleShader;
    s.bToggleShaderScreenSpace = m_bToggleShaderScreenSpace;
    s.dZoomX = m_ZoomX;
    s.dZoomY = m_ZoomY;

    m_controls.SaveState();

    m_OSD.OnHide();

    m_media_trans_control.close();

    if (UpdateCachedMediaState() == State_Running) {
        MediaControlPause(true);
    }

    ShowWindow(SW_HIDE);

    m_wndPlaylistBar.SavePlaylist();
    m_wndPlaylistBar.ClearExternalPlaylistIfInvalid();

    if (GetLoadState() == MLS::LOADED || GetLoadState() == MLS::LOADING) {
        CloseMedia();
    }

    s.WinLircClient.DisConnect();

    SendAPICommand(CMD_DISCONNECT, L"\0");  // according to CMD_NOTIFYENDOFSTREAM (ctrl+f it here), you're not supposed to send NULL here

    ASSERT(!m_bOpenMediaActive);

    #if !defined(_DEBUG) && USE_DRDUMP_CRASH_REPORTER && (MPC_VERSION_REV > 10)
    if (CrashReporter::IsEnabled()) {
        if (GetCurrentThreadId() != AfxGetApp()->m_nThreadID) {
            throw 0xdead;
        }
    }
    #endif

    if (GetLoadState() != MLS::CLOSED) {
#if MPC_VERSION_REV > 0
        AfxMessageBox(L"Unexpected state while closing.\n\nPlease contact the developers, so that we can analyze the problem.\n\nTo enable debug log:\nOptions > Advanced > DebugLogMask = 1\nLog file location:\n%APPDATA%\\MPC-HC\\player.log", MB_OK);
#endif
        if (USE_LOGGER(s)) {
            PLAYER_LOG(_T("CMainFrame::OnClose - Unexpected loadstate: %d"), (int)GetLoadState());
            FLUSH_LOGGER();
        }
        ASSERT(false);
        ForceCloseProcess();
    }   

    {
        CAutoLock ga(&lockGraphAccess);
        AfxGetMyApp()->SetClosingState();

        MSG msg;
        while (PeekMessage(&msg, nullptr, WM_GRAPHNOTIFY, WM_MPC_OPENCURPLAYLIST, PM_REMOVE)) {
            TRACE(L"Purged queued msg during player close: 0x%x\n", msg.message);
            ASSERT(false);
        }
        int pm = 0;
        while ((pm++ < 5) && PeekMessage(&msg, nullptr, WM_ACTIVATE, WM_ACTIVATE, PM_REMOVE)) {
            TRACE(L"Purged WM_ACTIVATE during player close\n");
        }
    }

    if (USE_LOGGER(s)) {
        PLAYER_LOG(_T("CMainFrame::OnClose - closing state has been set"));
        FLUSH_LOGGER();
    }

    __super::OnClose();
}

LPCTSTR CMainFrame::GetRecentFile() const
{
    auto& MRU = AfxGetAppSettings().MRU;
    MRU.ReadMediaHistory();
    for (int i = 0; i < MRU.GetSize(); i++) {
        if (MRU[i].fns.GetCount() > 0 && !MRU[i].fns.GetHead().IsEmpty()) {
            return MRU[i].fns.GetHead();
        }
    }
    return nullptr;
}

LRESULT CMainFrame::OnTaskBarRestart(WPARAM, LPARAM)
{
    m_bTrayIcon = false;
    ShowTrayIcon(AfxGetAppSettings().fTrayIcon);
    return 0;
}

LRESULT CMainFrame::OnNotifyIcon(WPARAM wParam, LPARAM lParam)
{
    if (HIWORD(lParam) != IDR_MAINFRAME) {
        return -1;
    }

    switch (LOWORD(lParam)) {
        case WM_LBUTTONDOWN:
            if (IsIconic()) {
                ShowWindow(SW_RESTORE);
            }
            CreateThumbnailToolbar();
            MoveVideoWindow();
            SetForegroundWindow();
            break;
        case WM_LBUTTONDBLCLK:
            PostMessage(WM_COMMAND, ID_FILE_OPENMEDIA);
            break;
        case WM_RBUTTONDOWN:
        case WM_CONTEXTMENU: {
            SetForegroundWindow();
            m_mainPopupMenu.GetSubMenu(0)->TrackPopupMenu(TPM_RIGHTBUTTON | TPM_NOANIMATION,
                GET_X_LPARAM(wParam), GET_Y_LPARAM(wParam), GetModalParent());
            PostMessage(WM_NULL);
            break;
        }
        case WM_MBUTTONDOWN: {
            OnPlayPlaypause();
            break;
        }
        case WM_MOUSEMOVE: {
            CString str;
            GetWindowText(str);
            SetTrayTip(str);
            break;
        }
        default:
            break;
    }

    return 0;
}

LRESULT CMainFrame::OnTaskBarThumbnailsCreate(WPARAM, LPARAM)
{
    return CreateThumbnailToolbar();
}

void CMainFrame::ShowTrayIcon(bool bShow)
{
    NOTIFYICONDATA nid = { sizeof(nid), m_hWnd, IDR_MAINFRAME };

    if (bShow) {
        if (!m_bTrayIcon) {
            nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP;
            nid.uCallbackMessage = WM_NOTIFYICON;
            nid.uVersion = NOTIFYICON_VERSION_4;
            nid.hIcon = (HICON)LoadImage(AfxGetInstanceHandle(), MAKEINTRESOURCE(IDR_MAINFRAME),
                                         IMAGE_ICON, 16, 16, LR_DEFAULTCOLOR);
            StringCchCopy(nid.szTip, _countof(nid.szTip), _T("MPC-HC"));
            if (Shell_NotifyIcon(NIM_ADD, &nid) && Shell_NotifyIcon(NIM_SETVERSION, &nid)) {
                m_bTrayIcon = true;
            }
        }
    } else {
        if (m_bTrayIcon) {
            Shell_NotifyIcon(NIM_DELETE, &nid);
            m_bTrayIcon = false;
            if (IsIconic()) {
                // if the window was minimized to tray - show it
                ShowWindow(SW_RESTORE);
            }
        }
    }
}

void CMainFrame::SetTrayTip(const CString& str)
{
    NOTIFYICONDATA tnid;
    tnid.cbSize = sizeof(NOTIFYICONDATA);
    tnid.hWnd = m_hWnd;
    tnid.uID = IDR_MAINFRAME;
    tnid.uFlags = NIF_TIP | NIF_SHOWTIP;
    StringCchCopy(tnid.szTip, _countof(tnid.szTip), str);
    Shell_NotifyIcon(NIM_MODIFY, &tnid);
}

BOOL CMainFrame::PreCreateWindow(CREATESTRUCT& cs)
{
    if (!__super::PreCreateWindow(cs)) {
        return FALSE;
    }

    cs.dwExStyle &= ~WS_EX_CLIENTEDGE;
    cs.lpszClass = MPC_WND_CLASS_NAME; //AfxRegisterWndClass(nullptr);

    return TRUE;
}

BOOL CMainFrame::PreTranslateMessage(MSG* pMsg)
{
    if (pMsg->message == WM_KEYDOWN) {
        if (pMsg->wParam == VK_ESCAPE) {
            bool fEscapeNotAssigned = !AssignedToCmd(VK_ESCAPE);

            if (fEscapeNotAssigned) {
                if (IsFullScreenMode()) {
                    OnViewFullscreen();
                    if (GetLoadState() == MLS::LOADED) {
                        PostMessage(WM_COMMAND, ID_PLAY_PAUSE);
                    }
                    return TRUE;
                } else if (IsCaptionHidden()) {
                    PostMessage(WM_COMMAND, ID_VIEW_PRESETS_NORMAL);
                    return TRUE;
                }
            }
        } else if (pMsg->wParam == VK_LEFT && m_pAMTuner) {
            PostMessage(WM_COMMAND, ID_NAVIGATE_SKIPBACK);
            return TRUE;
        } else if (pMsg->wParam == VK_RIGHT && m_pAMTuner) {
            PostMessage(WM_COMMAND, ID_NAVIGATE_SKIPFORWARD);
            return TRUE;
        }
    }

    if ((m_dwMenuBarVisibility & AFX_MBV_DISPLAYONFOCUS) && pMsg->message == WM_SYSKEYUP && pMsg->wParam == VK_F10 &&
            m_dwMenuBarState == AFX_MBS_VISIBLE) {
        // mfc doesn't hide menubar on f10, but we want to
        VERIFY(SetMenuBarState(AFX_MBS_HIDDEN));
        return FALSE;
    }

    if (pMsg->message == WM_KEYDOWN) {
        m_bAltDownClean = false;
    }
    if (pMsg->message == WM_SYSKEYDOWN) {
        m_bAltDownClean = (pMsg->wParam == VK_MENU);
    }
    if ((m_dwMenuBarVisibility & AFX_MBV_DISPLAYONFOCUS) && pMsg->message == WM_SYSKEYUP && pMsg->wParam == VK_MENU &&
            m_dwMenuBarState == AFX_MBS_HIDDEN) {
        // mfc shows menubar when Ctrl->Alt->K is released in reverse order, but we don't want to
        if (m_bAltDownClean) {
            VERIFY(SetMenuBarState(AFX_MBS_VISIBLE));
            return FALSE;
        }
        return TRUE;
    }

    // for compatibility with KatMouse and the like
    if (pMsg->message == WM_MOUSEWHEEL && pMsg->hwnd == m_hWnd) {
        pMsg->hwnd = m_wndView.m_hWnd;
        return FALSE;
    }

    return __super::PreTranslateMessage(pMsg);
}

void CMainFrame::RecalcLayout(BOOL bNotify)
{
    __super::RecalcLayout(bNotify);

    CRect r;
    GetWindowRect(&r);
    if (r.IsRectNull()) {
        ASSERT(false);
        return;
    }

    MINMAXINFO mmi;
    ZeroMemory(&mmi, sizeof(mmi));
    OnGetMinMaxInfo(&mmi);
    const POINT& min = mmi.ptMinTrackSize;
    if (r.Height() < min.y || r.Width() < min.x) {
        r |= CRect(r.TopLeft(), CSize(min));
        MoveWindow(r);
    }
    OSDBarSetPos();
    m_wndTabletFrame.SyncToOwner(!m_fFullScreen);
}

void CMainFrame::EnableDocking(DWORD dwDockStyle)
{
    ASSERT((dwDockStyle & ~(CBRS_ALIGN_ANY | CBRS_FLOAT_MULTI)) == 0);

    m_pFloatingFrameClass = RUNTIME_CLASS(CMPCThemeMiniDockFrameWnd);
    for (int i = 0; i < 4; i++) {
        if (dwDockBarMap[i][1] & dwDockStyle & CBRS_ALIGN_ANY) {
            CMPCThemeDockBar* pDock = (CMPCThemeDockBar*)GetControlBar(dwDockBarMap[i][0]);
            if (pDock == NULL) {
                pDock = DEBUG_NEW CMPCThemeDockBar;
                if (!pDock->Create(this,
                                   WS_CLIPSIBLINGS | WS_CLIPCHILDREN | WS_CHILD | WS_VISIBLE |
                                   dwDockBarMap[i][1], dwDockBarMap[i][0])) {
                    AfxThrowResourceException();
                }
            }
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// CMainFrame diagnostics

#ifdef _DEBUG
void CMainFrame::AssertValid() const
{
    __super::AssertValid();
}

void CMainFrame::Dump(CDumpContext& dc) const
{
    __super::Dump(dc);
}

#endif //_DEBUG

typedef HIMC(WINAPI* pfnImmAssociateContext)(HWND, HIMC);
void dynImmAssociateContext(HWND hWnd, HIMC himc) {
    HMODULE hImm32;
    pfnImmAssociateContext pImmAssociateContext;

    hImm32 = LoadLibrary(_T("imm32.dll"));
    if (NULL == hImm32) return; // No East Asian support
    pImmAssociateContext = (pfnImmAssociateContext)GetProcAddress(hImm32, "ImmAssociateContext");
    if (NULL == pImmAssociateContext) {
        FreeLibrary(hImm32);
        return;
    }
    pImmAssociateContext(hWnd, himc);
    FreeLibrary(hImm32);
}

/////////////////////////////////////////////////////////////////////////////
// CMainFrame message handlers
void CMainFrame::OnSetFocus(CWnd* pOldWnd)
{
    // forward focus to the view window
    if (IsWindow(m_wndView.m_hWnd)) {
        m_wndView.SetFocus();
        dynImmAssociateContext(m_wndView.m_hWnd, NULL);
    } else {
        dynImmAssociateContext(m_hWnd, NULL);
    }
}

BOOL CMainFrame::OnCmdMsg(UINT nID, int nCode, void* pExtra, AFX_CMDHANDLERINFO* pHandlerInfo)
{
    // let the view have first crack at the command
    if (m_wndView.OnCmdMsg(nID, nCode, pExtra, pHandlerInfo)) {
        return TRUE;
    }

    for (const auto& pair : m_controls.m_toolbars) {
        if (pair.second->OnCmdMsg(nID, nCode, pExtra, pHandlerInfo)) {
            return TRUE;
        }
    }

    for (const auto& pair : m_controls.m_panels) {
        if (pair.second->OnCmdMsg(nID, nCode, pExtra, pHandlerInfo)) {
            return TRUE;
        }
    }

    // otherwise, do default handling
    return __super::OnCmdMsg(nID, nCode, pExtra, pHandlerInfo);
}

void CMainFrame::OnGetMinMaxInfo(MINMAXINFO* lpMMI)
{
    auto setLarger = [](long & a, long b) {
        a = std::max(a, b);
    };

    const long saneSize = 110;
    const bool bMenuVisible = GetMenuBarVisibility() == AFX_MBV_KEEPVISIBLE || m_bShowingFloatingMenubar;

    // Begin with docked controls
    lpMMI->ptMinTrackSize = CPoint(m_controls.GetDockZonesMinSize(saneSize));

    if (bMenuVisible) {
        // Ensure that menubar will fit horizontally
        MENUBARINFO mbi = { sizeof(mbi) };
        GetMenuBarInfo(OBJID_MENU, 0, &mbi);
        long x = GetSystemMetrics(SM_CYMENU) / 2; // free space after menu
        CRect rect;
        for (int i = 0; GetMenuItemRect(m_hWnd, mbi.hMenu, i, &rect); i++) {
            x += rect.Width();
        }
        setLarger(lpMMI->ptMinTrackSize.x, x);
    }

    if (IsWindow(m_wndToolBar) && m_controls.ControlChecked(CMainFrameControls::Toolbar::CONTROLS)) {
        // Ensure that Controls toolbar will fit
        setLarger(lpMMI->ptMinTrackSize.x, m_wndToolBar.GetMinWidth());
    }

    // Ensure that window decorations will fit
    CRect decorationsRect;
    VERIFY(AdjustWindowRectEx(decorationsRect, GetWindowStyle(m_hWnd), bMenuVisible, GetWindowExStyle(m_hWnd)));
    lpMMI->ptMinTrackSize.x += decorationsRect.Width();
    lpMMI->ptMinTrackSize.y += decorationsRect.Height();

    // Final fence
    setLarger(lpMMI->ptMinTrackSize.x, GetSystemMetrics(SM_CXMIN));
    setLarger(lpMMI->ptMinTrackSize.y, GetSystemMetrics(SM_CYMIN));

    lpMMI->ptMaxTrackSize.x = GetSystemMetrics(SM_CXVIRTUALSCREEN) + decorationsRect.Width();
    lpMMI->ptMaxTrackSize.y = GetSystemMetrics(SM_CYVIRTUALSCREEN)
                              + ((GetStyle() & WS_THICKFRAME) ? GetSystemMetrics(SM_CYSIZEFRAME) : 0);

    OSDBarSetPos();
}

void CMainFrame::OnMove(int x, int y)
{
    __super::OnMove(x, y);

    if (m_bWasSnapped && IsZoomed()) {
        m_bWasSnapped = false;
    }

    WINDOWPLACEMENT wp;
    GetWindowPlacement(&wp);
    if (!m_bNeedZoomAfterFullscreenExit && !m_fFullScreen && IsWindowVisible() && wp.flags != WPF_RESTORETOMAXIMIZED && wp.showCmd != SW_SHOWMINIMIZED) {
        GetWindowRect(AfxGetAppSettings().rcLastWindowPos);
    }

    OSDBarSetPos();
    m_wndTabletFrame.SyncToOwner(!m_fFullScreen);
}

void CMainFrame::OnEnterSizeMove()
{
    if (m_bWasSnapped) {
        VERIFY(GetCursorPos(&m_snapStartPoint));
        GetWindowRect(m_snapStartRect);
    }
}

void CMainFrame::OnMoving(UINT fwSide, LPRECT pRect)
{
    if (AfxGetAppSettings().fSnapToDesktopEdges) {
        const CSize threshold(m_dpi.ScaleX(16), m_dpi.ScaleY(16));

        CRect rect(pRect);

        CRect windowRect;
        GetWindowRect(windowRect);

        if (windowRect.Size() != rect.Size()) {
            // aero snap
            return;
        }

        CPoint point;
        VERIFY(GetCursorPos(&point));

        if (m_bWasSnapped) {
            rect.MoveToXY(point - m_snapStartPoint + m_snapStartRect.TopLeft());
        }

        CRect areaRect;
        CMonitors::GetNearestMonitor(this).GetWorkAreaRect(areaRect);
        const CRect invisibleBorderSize = GetInvisibleBorderSize();
        areaRect.InflateRect(invisibleBorderSize);

        bool bSnapping = false;

        if (std::abs(rect.left - areaRect.left) < threshold.cx) {
            bSnapping = true;
            rect.MoveToX(areaRect.left);
        } else if (std::abs(rect.right - areaRect.right) < threshold.cx) {
            bSnapping = true;
            rect.MoveToX(areaRect.right - rect.Width());
        }
        if (std::abs(rect.top - areaRect.top) < threshold.cy) {
            bSnapping = true;
            rect.MoveToY(areaRect.top);
        } else if (std::abs(rect.bottom - areaRect.bottom) < threshold.cy) {
            bSnapping = true;
            rect.MoveToY(areaRect.bottom - rect.Height());
        }

        if (!m_bWasSnapped && bSnapping) {
            m_snapStartPoint = point;
            m_snapStartRect = pRect;
        }

        *pRect = rect;

        m_bWasSnapped = bSnapping;
    } else {
        m_bWasSnapped = false;
    }

    __super::OnMoving(fwSide, pRect);
    OSDBarSetPos();
}

void CMainFrame::OnSize(UINT nType, int cx, int cy)
{
    if (m_bTrayIcon && nType == SIZE_MINIMIZED) {
        ShowWindow(SW_HIDE);
    } else {
        __super::OnSize(nType, cx, cy);
        if (!m_bNeedZoomAfterFullscreenExit && IsWindowVisible() && !m_fFullScreen) {
            CAppSettings& s = AfxGetAppSettings();
            if (nType != SIZE_MAXIMIZED && nType != SIZE_MINIMIZED) {
                GetWindowRect(s.rcLastWindowPos);
            }
            s.nLastWindowType = nType;
        }
    }
    if (nType != SIZE_MINIMIZED) {
        OSDBarSetPos();
    }
    m_wndTabletFrame.SyncToOwner(!m_fFullScreen && nType != SIZE_MINIMIZED);
}

void CMainFrame::OnShowWindow(BOOL bShow, UINT nStatus)
{
    __super::OnShowWindow(bShow, nStatus);
    m_wndTabletFrame.SyncToOwner(bShow && !m_fFullScreen);
}

void CMainFrame::OnSizing(UINT nSide, LPRECT lpRect)
{
    __super::OnSizing(nSide, lpRect);

    if (m_fFullScreen) {
        return;
    }

    bool bCtrl = GetKeyState(VK_CONTROL) < 0;
    OnSizingFixWndToVideo(nSide, lpRect, bCtrl);
    OnSizingSnapToScreen(nSide, lpRect, bCtrl);
}

void CMainFrame::OnSizingFixWndToVideo(UINT nSide, LPRECT lpRect, bool bCtrl)
{
    const auto& s = AfxGetAppSettings();

    if (GetLoadState() != MLS::LOADED || s.iDefaultVideoSize == DVS_STRETCH ||
        bCtrl == s.fLimitWindowProportions || IsAeroSnapped() || (m_fAudioOnly && !m_wndView.IsCustomImgLoaded())) {
        return;
    }

    CSize videoSize = m_fAudioOnly ? m_wndView.GetLogoSize() : GetVideoSize();
    if (videoSize.cx == 0 || videoSize.cy == 0) {
        return;
    }

    CRect currentWindowRect, currentViewRect;
    GetWindowRect(currentWindowRect);
    m_wndView.GetWindowRect(currentViewRect);
    CSize controlsSize(currentWindowRect.Width() - currentViewRect.Width(),
                       currentWindowRect.Height() - currentViewRect.Height());

    const bool bToolbarsOnVideo = m_controls.ToolbarsCoverVideo();
    const bool bPanelsOnVideo = m_controls.PanelsCoverVideo();
    if (bPanelsOnVideo) {
        unsigned uTop, uLeft, uRight, uBottom;
        m_controls.GetVisibleDockZones(uTop, uLeft, uRight, uBottom);
        if (!bToolbarsOnVideo) {
            uBottom -= m_controls.GetVisibleToolbarsHeight();
        }
        controlsSize.cx -= uLeft + uRight;
        controlsSize.cy -= uTop + uBottom;
    } else if (bToolbarsOnVideo) {
        controlsSize.cy -= m_controls.GetVisibleToolbarsHeight();
    }

    CSize newWindowSize(lpRect->right - lpRect->left, lpRect->bottom - lpRect->top);

    newWindowSize -= controlsSize;

    switch (nSide) {
        case WMSZ_TOP:
        case WMSZ_BOTTOM:
            newWindowSize.cx = long(newWindowSize.cy * videoSize.cx / (double)videoSize.cy + 0.5);
            newWindowSize.cy = long(newWindowSize.cx * videoSize.cy / (double)videoSize.cx + 0.5);
            break;
        case WMSZ_TOPLEFT:
        case WMSZ_TOPRIGHT:
        case WMSZ_BOTTOMLEFT:
        case WMSZ_BOTTOMRIGHT:
        case WMSZ_LEFT:
        case WMSZ_RIGHT:
            newWindowSize.cy = long(newWindowSize.cx * videoSize.cy / (double)videoSize.cx + 0.5);
            newWindowSize.cx = long(newWindowSize.cy * videoSize.cx / (double)videoSize.cy + 0.5);
            break;
    }

    newWindowSize += controlsSize;

    switch (nSide) {
        case WMSZ_TOPLEFT:
            lpRect->left = lpRect->right - newWindowSize.cx;
            lpRect->top = lpRect->bottom - newWindowSize.cy;
            break;
        case WMSZ_TOP:
        case WMSZ_TOPRIGHT:
            lpRect->right = lpRect->left + newWindowSize.cx;
            lpRect->top = lpRect->bottom - newWindowSize.cy;
            break;
        case WMSZ_RIGHT:
        case WMSZ_BOTTOM:
        case WMSZ_BOTTOMRIGHT:
            lpRect->right = lpRect->left + newWindowSize.cx;
            lpRect->bottom = lpRect->top + newWindowSize.cy;
            break;
        case WMSZ_LEFT:
        case WMSZ_BOTTOMLEFT:
            lpRect->left = lpRect->right - newWindowSize.cx;
            lpRect->bottom = lpRect->top + newWindowSize.cy;
            break;
    }
    OSDBarSetPos();
}

void CMainFrame::OnSizingSnapToScreen(UINT nSide, LPRECT lpRect, bool bCtrl /*= false*/)
{
    const auto& s = AfxGetAppSettings();
    if (!s.fSnapToDesktopEdges)
        return;

    CRect areaRect;
    CMonitors::GetNearestMonitor(this).GetWorkAreaRect(areaRect);
    const CRect invisibleBorderSize = GetInvisibleBorderSize();
    areaRect.InflateRect(invisibleBorderSize);

    CRect& rect = *reinterpret_cast<CRect*>(lpRect);
    const CSize threshold(m_dpi.ScaleX(16), m_dpi.ScaleY(16));
    const auto SnapTo = [](LONG& val, LONG to, LONG threshold) {
        return (std::abs(val - to) < threshold && val != to) ? (val = to, true) : false;
    };

    CSize videoSize = GetVideoSize();

    if (bCtrl == s.fLimitWindowProportions || videoSize.cx == 0 || videoSize.cy == 0) {
        SnapTo(rect.left, areaRect.left, threshold.cx);
        SnapTo(rect.top, areaRect.top, threshold.cy);
        SnapTo(rect.right, areaRect.right, threshold.cx);
        SnapTo(rect.bottom, areaRect.bottom, threshold.cy);
        return;
    }

    const CRect rectOrig(rect);
    switch (nSide) {
        case WMSZ_TOPLEFT:
            if (SnapTo(rect.left, areaRect.left, threshold.cx)) {
                OnSizingFixWndToVideo(WMSZ_LEFT, &rect);
                rect.OffsetRect(0, rectOrig.bottom - rect.bottom);
                if (rect.top < areaRect.top && SnapTo(rect.top, areaRect.top, threshold.cy)) {
                    OnSizingFixWndToVideo(WMSZ_TOP, &rect);
                    rect.OffsetRect(rectOrig.right - rect.right, 0);
                }
            } else if (SnapTo(rect.top, areaRect.top, threshold.cy)) {
                OnSizingFixWndToVideo(WMSZ_TOP, &rect);
                rect.OffsetRect(rectOrig.right - rect.right, 0);
                if (rect.left < areaRect.left && SnapTo(rect.left, areaRect.left, threshold.cx)) {
                    OnSizingFixWndToVideo(WMSZ_LEFT, &rect);
                    rect.OffsetRect(0, rectOrig.bottom - rect.bottom);
                }
            }
            break;
        case WMSZ_TOP:
        case WMSZ_TOPRIGHT:
            if (SnapTo(rect.right, areaRect.right, threshold.cx)) {
                OnSizingFixWndToVideo(WMSZ_RIGHT, &rect);
                rect.OffsetRect(0, rectOrig.bottom - rect.bottom);
                if (rect.top < areaRect.top && SnapTo(rect.top, areaRect.top, threshold.cy)) {
                    OnSizingFixWndToVideo(WMSZ_TOP, &rect);
                    rect.OffsetRect(rectOrig.left - rect.left, 0);
                }
            }
            else if (SnapTo(rect.top, areaRect.top, threshold.cy)) {
                OnSizingFixWndToVideo(WMSZ_TOP, &rect);
                rect.OffsetRect(rectOrig.left - rect.left, 0);
                if (areaRect.right < rect.right && SnapTo(rect.right, areaRect.right, threshold.cx)) {
                    OnSizingFixWndToVideo(WMSZ_RIGHT, &rect);
                    rect.OffsetRect(0, rectOrig.bottom - rect.bottom);
                }
            }
            break;
        case WMSZ_RIGHT:
        case WMSZ_BOTTOM:
        case WMSZ_BOTTOMRIGHT:
            if (SnapTo(rect.right, areaRect.right, threshold.cx)) {
                OnSizingFixWndToVideo(WMSZ_RIGHT, &rect);
                if (areaRect.bottom < rect.bottom && SnapTo(rect.bottom, areaRect.bottom, threshold.cy)) {
                    OnSizingFixWndToVideo(WMSZ_BOTTOM, &rect);
                }
            } else if (SnapTo(rect.bottom, areaRect.bottom, threshold.cy)) {
                OnSizingFixWndToVideo(WMSZ_BOTTOM, &rect);
                if (areaRect.right < rect.right && SnapTo(rect.right, areaRect.right, threshold.cx)) {
                    OnSizingFixWndToVideo(WMSZ_RIGHT, &rect);
                }
            }
            break;
        case WMSZ_LEFT:
        case WMSZ_BOTTOMLEFT:
            if (SnapTo(rect.left, areaRect.left, threshold.cx)) {
                OnSizingFixWndToVideo(WMSZ_LEFT, &rect);
                if (areaRect.bottom < rect.bottom && SnapTo(rect.bottom, areaRect.bottom, threshold.cy)) {
                    OnSizingFixWndToVideo(WMSZ_BOTTOM, &rect);
                    rect.OffsetRect(rectOrig.right - rect.right, 0);
                }
            } else if (SnapTo(rect.bottom, areaRect.bottom, threshold.cy)) {
                OnSizingFixWndToVideo(WMSZ_BOTTOM, &rect);
                rect.OffsetRect(rectOrig.right - rect.right, 0);
                if (rect.left < areaRect.left && SnapTo(rect.left, areaRect.left, threshold.cx)) {
                    OnSizingFixWndToVideo(WMSZ_LEFT, &rect);
                }
            }
            break;
    }
}

void CMainFrame::OnExitSizeMove()
{
    if (m_wndView.Dragging()) {
        // HACK: windowed (not renderless) video renderers may not produce WM_MOUSEMOVE message here
        UpdateControlState(CMainFrame::UPDATE_CHILDVIEW_CURSOR_HACK);
    }
}

void CMainFrame::OnDisplayChange() // untested, not sure if it's working...
{
    TRACE(_T("*** CMainFrame::OnDisplayChange()\n"));

    if (USE_LOGGER(AfxGetAppSettings())) {
        PLAYER_LOG(_T("CMainFrame::OnDisplayChange"));
        FLUSH_LOGGER();
    }

    if (GetLoadState() == MLS::LOADED) {
        if (m_bOpenedThroughThread && m_pGraphThread && m_pGraphThread->m_hThread) {
            CAMMsgEvent e;
            if (m_pGraphThread->PostThreadMessage(CGraphThread::TM_DISPLAY_CHANGE, (WPARAM)0, (LPARAM)&e)) {
                e.WaitMsg();
            } else {
                DisplayChange();
            }
        } else {
            DisplayChange();
        }
    }

    if (HasDedicatedFSVideoWindow()) {
        MONITORINFO MonitorInfo;
        HMONITOR    hMonitor;

        ZeroMemory(&MonitorInfo, sizeof(MonitorInfo));
        MonitorInfo.cbSize = sizeof(MonitorInfo);

        hMonitor = MonitorFromWindow(m_pDedicatedFSVideoWnd->m_hWnd, 0);
        if (GetMonitorInfo(hMonitor, &MonitorInfo)) {
            CRect MonitorRect = CRect(MonitorInfo.rcMonitor);
            m_pDedicatedFSVideoWnd->SetWindowPos(nullptr,
                                           MonitorRect.left,
                                           MonitorRect.top,
                                           MonitorRect.Width(),
                                           MonitorRect.Height(),
                                           SWP_NOZORDER);
            MoveVideoWindow();
        }
    }
}

void CMainFrame::OnWindowPosChanging(WINDOWPOS* lpwndpos)
{
    if (!(lpwndpos->flags & SWP_NOMOVE) && IsFullScreenMainFrame()) {
        HMONITOR hm = MonitorFromPoint(CPoint(lpwndpos->x, lpwndpos->y), MONITOR_DEFAULTTONULL);
        MONITORINFO mi = { sizeof(mi) };
        if (GetMonitorInfo(hm, &mi)) {
            lpwndpos->flags &= ~SWP_NOSIZE;
            lpwndpos->cx = mi.rcMonitor.right - mi.rcMonitor.left;
            lpwndpos->cy = mi.rcMonitor.bottom - mi.rcMonitor.top;
            lpwndpos->x = mi.rcMonitor.left;
            lpwndpos->y = mi.rcMonitor.top;
        }
    }
    __super::OnWindowPosChanging(lpwndpos);
}

LRESULT CMainFrame::OnDpiChanged(WPARAM wParam, LPARAM lParam)
{
    m_dpi.Override(LOWORD(wParam), HIWORD(wParam));
    m_eventc.FireEvent(MpcEvent::DPI_CHANGED);

    if (!restoringWindowRect) { //do not adjust for DPI if restoring saved window position
        MoveWindow(reinterpret_cast<RECT*>(lParam));
    }
    CMPCThemeUtil::GetMetrics(true); //force reset metrics used by util class
    CMPCThemeMenu::clearDimensions();
    ReloadMenus();

    RecalcLayout();
    m_wndPreView.ScaleFont();
    m_wndTabletFrame.SyncToOwner(!m_fFullScreen);
    return 0;
}

void CMainFrame::OnSysCommand(UINT nID, LPARAM lParam)
{
    if ((nID & 0xFFF0) == SC_SCREENSAVE || (nID & 0xFFF0) == SC_MONITORPOWER) {
        // Only stop screensaver if video playing
        if (!m_fAudioOnly && !m_fEndOfStream && GetLoadState() == MLS::LOADED && GetMediaState() == State_Running) {
            TRACE(_T("SC_SCREENSAVE, nID = %u, lParam = %d\n"), nID, lParam);
            return;
        }
    }
    if ((nID & 0xFFF0) == SC_CLOSE) {
        OnClose();
        return;
    }

    if (USE_LOGGER(AfxGetAppSettings())) {
        PLAYER_LOG(_T("CMainFrame::OnSysCommand - nID=0x%x lParam=%ld"), nID, lParam);
    }

    __super::OnSysCommand(nID, lParam);
}

void CMainFrame::OnActivateApp(BOOL bActive, DWORD dwThreadID)
{
    __super::OnActivateApp(bActive, dwThreadID);

    m_timerOneTime.Unsubscribe(TimerOneTimeSubscriber::PLACE_FULLSCREEN_UNDER_ACTIVE_WINDOW);

    if (IsFullScreenMainFrame()) {
        if (bActive) {
            // keep the fullscreen window on top while it's active,
            // we don't want notification pop-ups to cover it
            SetWindowPos(&wndTopMost, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
        } else {
            // don't keep the fullscreen window on top when it's not active,
            // we want to be able to switch to other windows nicely
            struct {
                void operator()() const {
                    CMainFrame* pMainFrame = AfxGetMainFrame();
                    if (!pMainFrame || !pMainFrame->m_fFullScreen || pMainFrame->WindowExpectedOnTop() || pMainFrame->m_bExtOnTop) {
                        return;
                    }
                    // place our window under the new active window
                    // when we can't determine that window, we try later
                    if (CWnd* pActiveWnd = GetForegroundWindow()) {
                        bool bMoved = false;
                        if (CWnd* pActiveRootWnd = pActiveWnd->GetAncestor(GA_ROOT)) {
                            const DWORD dwStyle = pActiveRootWnd->GetStyle();
                            const DWORD dwExStyle = pActiveRootWnd->GetExStyle();
                            if (!(dwStyle & WS_CHILD) && !(dwStyle & WS_POPUP) && !(dwExStyle & WS_EX_TOPMOST)) {
                                if (CWnd* pLastWnd = GetDesktopWindow()->GetTopWindow()) {
                                    while (CWnd* pWnd = pLastWnd->GetNextWindow(GW_HWNDNEXT)) {
                                        if (*pLastWnd == *pActiveRootWnd) {
                                            pMainFrame->SetWindowPos(
                                                pWnd, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
                                            bMoved = true;
                                            break;
                                        }
                                        pLastWnd = pWnd;
                                    }
                                } else {
                                    ASSERT(FALSE);
                                }
                            }
                        }
                        if (!bMoved) {
                            pMainFrame->SetWindowPos(
                                &wndNoTopMost, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
                        }
                    } else {
                        pMainFrame->m_timerOneTime.Subscribe(
                            TimerOneTimeSubscriber::PLACE_FULLSCREEN_UNDER_ACTIVE_WINDOW, *this, 1);
                    }
                }
            } placeUnder;
            placeUnder();
        }
    }
}

LRESULT CMainFrame::OnAppCommand(WPARAM wParam, LPARAM lParam)
{
    UINT cmd  = GET_APPCOMMAND_LPARAM(lParam);
    UINT uDevice = GET_DEVICE_LPARAM(lParam);

    if (uDevice != FAPPCOMMAND_OEM && cmd != 0
            || cmd == APPCOMMAND_MEDIA_PLAY
            || cmd == APPCOMMAND_MEDIA_PAUSE
            || cmd == APPCOMMAND_MEDIA_CHANNEL_UP
            || cmd == APPCOMMAND_MEDIA_CHANNEL_DOWN
            || cmd == APPCOMMAND_MEDIA_RECORD
            || cmd == APPCOMMAND_MEDIA_FAST_FORWARD
            || cmd == APPCOMMAND_MEDIA_REWIND) {
        const CAppSettings& s = AfxGetAppSettings();

        BOOL fRet = FALSE;

        POSITION pos = s.wmcmds.GetHeadPosition();
        while (pos) {
            const wmcmd& wc = s.wmcmds.GetNext(pos);
            if (wc.appcmd == cmd && TRUE == SendMessage(WM_COMMAND, wc.cmd)) {
                fRet = TRUE;
            }
        }

        if (fRet) {
            return TRUE;
        }
    }

    return Default();
}

void CMainFrame::OnRawInput(UINT nInputcode, HRAWINPUT hRawInput)
{
    const CAppSettings& s = AfxGetAppSettings();
    UINT nMceCmd = AfxGetMyApp()->GetRemoteControlCode(nInputcode, hRawInput);

    switch (nMceCmd) {
        case MCE_DETAILS:
        case MCE_GUIDE:
        case MCE_TVJUMP:
        case MCE_STANDBY:
        case MCE_OEM1:
        case MCE_OEM2:
        case MCE_MYTV:
        case MCE_MYVIDEOS:
        case MCE_MYPICTURES:
        case MCE_MYMUSIC:
        case MCE_RECORDEDTV:
        case MCE_DVDANGLE:
        case MCE_DVDAUDIO:
        case MCE_DVDMENU:
        case MCE_DVDSUBTITLE:
        case MCE_RED:
        case MCE_GREEN:
        case MCE_YELLOW:
        case MCE_BLUE:
        case MCE_MEDIA_NEXTTRACK:
        case MCE_MEDIA_PREVIOUSTRACK:
            POSITION pos = s.wmcmds.GetHeadPosition();
            while (pos) {
                const wmcmd& wc = s.wmcmds.GetNext(pos);
                if (wc.appcmd == nMceCmd) {
                    SendMessage(WM_COMMAND, wc.cmd);
                    break;
                }
            }
            break;
    }
}

LRESULT CMainFrame::OnHotKey(WPARAM wParam, LPARAM lParam)
{
    if (wParam == 0) {
        ASSERT(false);
        return FALSE;
    }

    const CAppSettings& s = AfxGetAppSettings();
    BOOL fRet = FALSE;

    if (GetActiveWindow() == this || s.fGlobalMedia == TRUE) {
        POSITION pos = s.wmcmds.GetHeadPosition();

        while (pos) {
            const wmcmd& wc = s.wmcmds.GetNext(pos);
            if (wc.appcmd == wParam && TRUE == SendMessage(WM_COMMAND, wc.cmd)) {
                fRet = TRUE;
            }
        }
    }

    return fRet;
}

bool g_bNoDuration = false;
bool g_bExternalSubtitleTime = false;
bool g_bExternalSubtitle = false;
double g_dRate = 1.0;

void CMainFrame::OnTimer(UINT_PTR nIDEvent)
{
    switch (nIDEvent) {
        case TIMER_WINDOW_FULLSCREEN:
            if (AfxGetAppSettings().iFullscreenDelay > 0 && IsWindows8OrGreater()) {//DWMWA_CLOAK not supported on 7
                BOOL setEnabled = FALSE;
                ::DwmSetWindowAttribute(m_hWnd, DWMWA_CLOAK, &setEnabled, sizeof(setEnabled));
            }
            KillTimer(TIMER_WINDOW_FULLSCREEN);
            delayingFullScreen = false;
            break;
        case TIMER_STREAMPOSPOLLER:
            if (GetLoadState() == MLS::LOADED) {
                REFERENCE_TIME rtNow = 0, rtDur = 0;
                switch (GetPlaybackMode()) {
                    case PM_FILE:
                        g_bExternalSubtitleTime = false;
                        if (m_pGB && m_pMS) {
                            m_pMS->GetCurrentPosition(&rtNow);
                            if (!m_pGB || !m_pMS) {
                                // can happen extremely rarely based on crash dump
                                // no idea how, since closing of graph is initiated from this same thread
                                ASSERT(false);
                                return;
                            }
                            m_pMS->GetDuration(&rtDur);

                            if ((abRepeat.positionA && rtNow < abRepeat.positionA || abRepeat.positionB && rtNow >= abRepeat.positionB) && GetMediaState() != State_Stopped) {
                                PerformABRepeat();
                                return;
                            }

                            auto* pMRU = &AfxGetAppSettings().MRU;
                            if (m_bRememberFilePos && !m_fEndOfStream) {
                                pMRU->UpdateCurrentFilePosition(rtNow);
                            }

                            // Casimir666 : autosave subtitle sync after play
                            if (m_nCurSubtitle >= 0 && m_rtCurSubPos != rtNow) {
                                if (m_lSubtitleShift) {
                                    if (m_wndSubresyncBar.SaveToDisk()) {
                                        m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_AG_SUBTITLES_SAVED), 500);
                                    } else {
                                        m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_MAINFRM_4));
                                    }
                                }
                                m_nCurSubtitle = -1;
                                m_lSubtitleShift = 0;
                            }

                            m_wndStatusBar.SetStatusTimer(rtNow, rtDur, IsSubresyncBarVisible(), GetTimeFormat());

                            if (AfxGetAppSettings().bAutoCopySubtitleToClipboard && rtNow >= m_rtNextAutoCopySubtitle) {
                                m_rtNextAutoCopySubtitle = CopyCurrentSubtitleToClipboard(rtNow);
                            }
                        }
                        break;
                    case PM_DVD:
                        g_bExternalSubtitleTime = true;
                        if (m_pDVDI) {
                            DVD_PLAYBACK_LOCATION2 Location;
                            if (m_pDVDI->GetCurrentLocation(&Location) == S_OK) {
                                double fps = Location.TimeCodeFlags == DVD_TC_FLAG_25fps ? 25.0
                                             : Location.TimeCodeFlags == DVD_TC_FLAG_30fps ? 30.0
                                             : Location.TimeCodeFlags == DVD_TC_FLAG_DropFrame ? 30 / 1.001
                                             : 25.0;

                                rtNow = HMSF2RT(Location.TimeCode, fps);

                                if (abRepeat.positionB && rtNow >= abRepeat.positionB && GetMediaState() != State_Stopped) {
                                    PerformABRepeat();
                                    return;
                                }

                                DVD_HMSF_TIMECODE tcDur;
                                ULONG ulFlags;
                                if (SUCCEEDED(m_pDVDI->GetTotalTitleTime(&tcDur, &ulFlags))) {
                                    rtDur = HMSF2RT(tcDur, fps);
                                }
                                if (m_pSubClock) {
                                    m_pSubClock->SetTime(rtNow);
                                }
                            }
                        }
                        m_wndStatusBar.SetStatusTimer(rtNow, rtDur, IsSubresyncBarVisible(), GetTimeFormat());
                        break;
                    case PM_ANALOG_CAPTURE:
                        g_bExternalSubtitleTime = true;
                        if (m_fCapturing) {
                            if (m_wndCaptureBar.m_capdlg.m_pMux) {
                                CComQIPtr<IMediaSeeking> pMuxMS = m_wndCaptureBar.m_capdlg.m_pMux;
                                if (!pMuxMS || FAILED(pMuxMS->GetCurrentPosition(&rtNow))) {
                                    if (m_pMS) {
                                        m_pMS->GetCurrentPosition(&rtNow);
                                    }
                                }
                            }
                            if (m_rtDurationOverride >= 0) {
                                rtDur = m_rtDurationOverride;
                            }
                        }
                        break;
                    case PM_DIGITAL_CAPTURE:
                        g_bExternalSubtitleTime = true;
                        m_pMS->GetCurrentPosition(&rtNow);
                        break;
                    default:
                        ASSERT(FALSE);
                        break;
                }

                g_bNoDuration = rtDur <= 0;
                m_wndSeekBar.Enable(!g_bNoDuration);
                m_wndSeekBar.SetRange(0, rtDur);
                m_wndSeekBar.SetPos(rtNow);
                m_wndSeekBar.UpdateTime();
                m_OSD.SetRange(rtDur);
                m_OSD.SetPos(rtNow);
                m_Lcd.SetMediaRange(0, rtDur);
                m_Lcd.SetMediaPos(rtNow);

                if (m_pCAP) {
                    if (g_bExternalSubtitleTime) {
                        m_pCAP->SetTime(rtNow);
                    }
                    m_wndSubresyncBar.SetTime(rtNow);
                    m_wndSubresyncBar.SetFPS(m_pCAP->GetFPS());
                }
                if (g_bExternalSubtitleTime && (m_iStreamPosPollerInterval > 40)) {
                    AdjustStreamPosPoller(true);
                }
            }
            break;
        case TIMER_STREAMPOSPOLLER2:
            if (GetLoadState() == MLS::LOADED) {
                switch (GetPlaybackMode()) {
                    case PM_FILE:
                    // no break
                    case PM_DVD:
                        // Update media transport controls timeline (throttled)
                        MediaTransportControlUpdateTimeline();
                        if (AfxGetAppSettings().fShowCurrentTimeInOSD && m_OSD.CanShowMessage()) {
                            m_OSD.DisplayTime(m_wndStatusBar.GetStatusTimer());
                        }
                        break;
                    case PM_DIGITAL_CAPTURE: {
                        EventDescriptor& NowNext = m_pDVBState->NowNext;
                        time_t tNow;
                        time(&tNow);
                        if (NowNext.duration > 0 && tNow >= NowNext.startTime && tNow <= NowNext.startTime + NowNext.duration) {
                            REFERENCE_TIME rtNow = REFERENCE_TIME(tNow - NowNext.startTime) * 10000000;
                            REFERENCE_TIME rtDur = REFERENCE_TIME(NowNext.duration) * 10000000;
                            m_wndStatusBar.SetStatusTimer(rtNow, rtDur, false, TIME_FORMAT_MEDIA_TIME);
                            if (AfxGetAppSettings().fShowCurrentTimeInOSD && m_OSD.CanShowMessage()) {
                                m_OSD.DisplayTime(m_wndStatusBar.GetStatusTimer());
                            }
                        } else {
                            m_wndStatusBar.SetStatusTimer(ResStr(IDS_CAPTURE_LIVE));
                        }
                    }
                    break;
                    case PM_ANALOG_CAPTURE:
                        if (!m_fCapturing) {
                            CString str(StrRes(IDS_CAPTURE_LIVE));
                            long lChannel = 0, lVivSub = 0, lAudSub = 0;
                            if (m_pAMTuner
                                    && m_wndCaptureBar.m_capdlg.IsTunerActive()
                                    && SUCCEEDED(m_pAMTuner->get_Channel(&lChannel, &lVivSub, &lAudSub))) {
                                str.AppendFormat(_T(" (ch%ld)"), lChannel);
                            }
                            m_wndStatusBar.SetStatusTimer(str);
                        }
                        break;
                    default:
                        ASSERT(FALSE);
                        break;
                }
            }
            break;
        case TIMER_STATS: {
            const CAppSettings& s = AfxGetAppSettings();
            if (m_wndStatsBar.IsVisible()) {
                CString rate;
                rate.Format(_T("%.3fx"), m_dSpeedRate);
                if (m_pQP) {
                    CString info;
                    int tmp, tmp1;

                    if (SUCCEEDED(m_pQP->get_AvgFrameRate(&tmp))) { // We hang here due to a lock that never gets released.
                        info.Format(_T("%d.%02d (%s)"), tmp / 100, tmp % 100, rate.GetString());
                    } else {
                        info = _T("-");
                    }
                    m_wndStatsBar.SetLine(StrRes(IDS_AG_FRAMERATE), info);

                    if (SUCCEEDED(m_pQP->get_FramesDrawn(&tmp))
                        && SUCCEEDED(m_pQP->get_FramesDroppedInRenderer(&tmp1))) {
                        info.Format(IDS_MAINFRM_6, tmp, tmp1);
                    } else {
                        info = _T("-");
                    }
                    m_wndStatsBar.SetLine(StrRes(IDS_AG_FRAMES), info);

                    if (s.iDSVideoRendererType != VIDRNDT_DS_MADVR && s.iDSVideoRendererType != VIDRNDT_DS_EVR && s.iDSVideoRendererType != VIDRNDT_DS_SYNC) {
                        if (SUCCEEDED(m_pQP->get_AvgSyncOffset(&tmp))
                            && SUCCEEDED(m_pQP->get_DevSyncOffset(&tmp1))) {
                            info.Format(IDS_STATSBAR_SYNC_OFFSET_FORMAT, tmp, tmp1);
                        } else {
                            info = _T("-");
                        }
                        m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_SYNC_OFFSET), info);

                        if (SUCCEEDED(m_pQP->get_Jitter(&tmp))) {
                            info.Format(_T("%d ms"), tmp);
                        } else {
                            info = _T("-");
                        }
                        m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_JITTER), info);
                    }
                } else {
                    m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_PLAYBACK_RATE), rate);
                }

                if (m_pBI) {
                    CString sInfo;

                    for (int i = 0, j = m_pBI->GetCount(); i < j; i++) {
                        int samples, size;
                        if (S_OK == m_pBI->GetStatus(i, samples, size) && (i < 2 || size > 0)) { // third pin is usually subs 
                            sInfo.AppendFormat(_T("[P%d] %03d samples / %d KB   "), i, samples, size / 1024);
                        }
                    }

                    if (!sInfo.IsEmpty()) {
                        //sInfo.AppendFormat(_T("(p%lu)"), m_pBI->GetPriority());
                        m_wndStatsBar.SetLine(StrRes(IDS_AG_BUFFERS), sInfo);
                    }
                }

                {
                    // IBitRateInfo
                    CString sInfo;
                    BeginEnumFilters(m_pGB, pEF, pBF) {
                        unsigned i = 0;
                        BeginEnumPins(pBF, pEP, pPin) {
                            if (CComQIPtr<IBitRateInfo> pBRI = pPin) {
                                DWORD nAvg = pBRI->GetAverageBitRate() / 1000;

                                if (nAvg > 0) {
                                    sInfo.AppendFormat(_T("[P%u] %lu/%lu kb/s   "), i, nAvg, pBRI->GetCurrentBitRate() / 1000);
                                }
                            }
                            i++;
                        }
                        EndEnumPins;

                        if (!sInfo.IsEmpty()) {
                            m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_BITRATE), sInfo + ResStr(IDS_STATSBAR_BITRATE_AVG_CUR));
                            sInfo.Empty();
                        }
                    }
                    EndEnumFilters;
                }
            }

            if (GetPlaybackMode() == PM_DVD) { // we also use this timer to update the info panel for DVD playback
                ULONG ulAvailable, ulCurrent;

                CString Location(_T('-'));
                CString Audio(_T('-'));
                CString Video(_T('-'));

                DVD_PLAYBACK_LOCATION2 loc;
                ULONG ulNumOfVolumes, ulVolume;
                DVD_DISC_SIDE Side;
                ULONG ulNumOfTitles;
                ULONG ulNumOfChapters;

                // Location
                if (SUCCEEDED(m_pDVDI->GetCurrentLocation(&loc))
                        && SUCCEEDED(m_pDVDI->GetNumberOfChapters(loc.TitleNum, &ulNumOfChapters))
                        && SUCCEEDED(m_pDVDI->GetDVDVolumeInfo(&ulNumOfVolumes, &ulVolume, &Side, &ulNumOfTitles))) {
                    Location.Format(IDS_MAINFRM_9,
                                    ulVolume, ulNumOfVolumes,
                                    loc.TitleNum, ulNumOfTitles,
                                    loc.ChapterNum, ulNumOfChapters);
                    ULONG tsec = (loc.TimeCode.bHours * 3600)
                                 + (loc.TimeCode.bMinutes * 60)
                                 + (loc.TimeCode.bSeconds);
                    /* This might not always work, such as on resume */
                    if (loc.ChapterNum != m_lCurrentChapter) {
                        m_lCurrentChapter = loc.ChapterNum;
                        m_lChapterStartTime = tsec;
                    } else {
                        /* If a resume point was used, and the user chapter jumps,
                        then it might do some funky time jumping.  Try to 'fix' the
                        chapter start time if this happens */
                        if (m_lChapterStartTime > tsec) {
                            m_lChapterStartTime = tsec;
                        }
                    }
                }

                // Video
                DVD_VideoAttributes VATR;
                if (SUCCEEDED(m_pDVDI->GetCurrentAngle(&ulAvailable, &ulCurrent))
                        && SUCCEEDED(m_pDVDI->GetCurrentVideoAttributes(&VATR))) {
                    Video.Format(IDS_MAINFRM_10,
                                 ulCurrent, ulAvailable,
                                 VATR.ulSourceResolutionX, VATR.ulSourceResolutionY, VATR.ulFrameRate,
                                 VATR.ulAspectX, VATR.ulAspectY);
                    m_statusbarVideoSize.Format(_T("%dx%d"), VATR.ulSourceResolutionX, VATR.ulSourceResolutionY);
                    m_statusbarVideoFormat = VATR.Compression == DVD_VideoCompression_MPEG1 ? L"MPG1" : VATR.Compression == DVD_VideoCompression_MPEG2 ? L"MPG2" : L"";
                }

                // Audio
                DVD_AudioAttributes AATR;
                if (SUCCEEDED(m_pDVDI->GetCurrentAudio(&ulAvailable, &ulCurrent))
                        && SUCCEEDED(m_pDVDI->GetAudioAttributes(ulCurrent, &AATR))) {
                    CString lang;
                    if (AATR.Language) {
                        GetLocaleString(AATR.Language, LOCALE_SENGLANGUAGE, lang);
                        currentAudioLang = lang;
                    } else {
                        lang.Format(IDS_AG_UNKNOWN, ulCurrent + 1);
                        currentAudioLang.Empty();
                    }

                    switch (AATR.LanguageExtension) {
                        case DVD_AUD_EXT_NotSpecified:
                        default:
                            break;
                        case DVD_AUD_EXT_Captions:
                            lang += _T(" (Captions)");
                            break;
                        case DVD_AUD_EXT_VisuallyImpaired:
                            lang += _T(" (Visually Impaired)");
                            break;
                        case DVD_AUD_EXT_DirectorComments1:
                            lang += _T(" (Director Comments 1)");
                            break;
                        case DVD_AUD_EXT_DirectorComments2:
                            lang += _T(" (Director Comments 2)");
                            break;
                    }

                    CString format = GetDVDAudioFormatName(AATR);
                    m_statusbarAudioFormat.Format(L"%s %dch", format, AATR.bNumberOfChannels);

                    Audio.Format(IDS_MAINFRM_11,
                                 lang.GetString(),
                                 format.GetString(),
                                 AATR.dwFrequency,
                                 AATR.bQuantization,
                                 AATR.bNumberOfChannels,
                                 ResStr(AATR.bNumberOfChannels > 1 ? IDS_MAINFRM_13 : IDS_MAINFRM_12).GetString());

                    m_wndStatusBar.SetStatusBitmap(
                        AATR.bNumberOfChannels == 1 ? IDB_AUDIOTYPE_MONO
                        : AATR.bNumberOfChannels >= 2 ? IDB_AUDIOTYPE_STEREO
                        : IDB_AUDIOTYPE_NOAUDIO);
                }

                if (m_wndInfoBar.IsVisible()) {
                    m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_LOCATION), Location);
                    m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_VIDEO), Video);
                    m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_AUDIO), Audio);

                    // Subtitles
                    CString Subtitles(_T('-'));
                    BOOL bIsDisabled;
                    DVD_SubpictureAttributes SATR;
                    if (SUCCEEDED(m_pDVDI->GetCurrentSubpicture(&ulAvailable, &ulCurrent, &bIsDisabled))
                        && SUCCEEDED(m_pDVDI->GetSubpictureAttributes(ulCurrent, &SATR))) {
                        CString lang;
                        GetLocaleString(SATR.Language, LOCALE_SENGLANGUAGE, lang);

                        switch (SATR.LanguageExtension) {
                        case DVD_SP_EXT_NotSpecified:
                        default:
                            break;
                        case DVD_SP_EXT_Caption_Normal:
                            lang += _T("");
                            break;
                        case DVD_SP_EXT_Caption_Big:
                            lang += _T(" (Big)");
                            break;
                        case DVD_SP_EXT_Caption_Children:
                            lang += _T(" (Children)");
                            break;
                        case DVD_SP_EXT_CC_Normal:
                            lang += _T(" (CC)");
                            break;
                        case DVD_SP_EXT_CC_Big:
                            lang += _T(" (CC Big)");
                            break;
                        case DVD_SP_EXT_CC_Children:
                            lang += _T(" (CC Children)");
                            break;
                        case DVD_SP_EXT_Forced:
                            lang += _T(" (Forced)");
                            break;
                        case DVD_SP_EXT_DirectorComments_Normal:
                            lang += _T(" (Director Comments)");
                            break;
                        case DVD_SP_EXT_DirectorComments_Big:
                            lang += _T(" (Director Comments, Big)");
                            break;
                        case DVD_SP_EXT_DirectorComments_Children:
                            lang += _T(" (Director Comments, Children)");
                            break;
                        }

                        if (bIsDisabled) {
                            lang = _T("-");
                        }

                        Subtitles.Format(_T("%s"),
                            lang.GetString());
                    }

                    m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_SUBTITLES), Subtitles);
                }
            } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
                if (m_pDVBState->bActive) {
                    CComQIPtr<IBDATuner> pTun = m_pGB;
                    BOOLEAN bPresent, bLocked;
                    LONG lDbStrength, lPercentQuality;
                    CString Signal;

                    if (SUCCEEDED(pTun->GetStats(bPresent, bLocked, lDbStrength, lPercentQuality)) && bPresent) {
                        Signal.Format(IDS_STATSBAR_SIGNAL_FORMAT, (int)lDbStrength, lPercentQuality);
                        m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_SIGNAL), Signal);
                    }
                } else {
                    m_wndStatsBar.SetLine(StrRes(IDS_STATSBAR_SIGNAL), _T("-"));
                }
            } else if (GetPlaybackMode() == PM_FILE) {
                if (m_wndInfoBar.IsVisible() || s.hMasterWnd) {
                    OpenSetupInfoBar(false);
                }
                if (s.iTitleBarTextStyle == 1 && s.fTitleBarTextTitle) {
                    OpenSetupWindowTitle();
                }
                MediaTransportControlSetMedia();
                SendNowPlayingToApi(false);
            }

            if (m_CachedFilterState == State_Running && !m_fAudioOnly) {
                if (s.bPreventDisplaySleep) {
                    BOOL fActive = FALSE;
                    if (SystemParametersInfo(SPI_GETSCREENSAVEACTIVE, 0, &fActive, 0) && fActive) {
                        SystemParametersInfo(SPI_SETSCREENSAVEACTIVE, FALSE, nullptr, SPIF_SENDWININICHANGE);
                        SystemParametersInfo(SPI_SETSCREENSAVEACTIVE, fActive, nullptr, SPIF_SENDWININICHANGE);
                    }

                    // prevent screensaver activate, monitor sleep/turn off after playback
                    SetThreadExecutionState(ES_SYSTEM_REQUIRED | ES_DISPLAY_REQUIRED);
                }
            }
        }
        break;
        case TIMER_UNLOAD_UNUSED_EXTERNAL_OBJECTS: {
            if (GetPlaybackMode() == PM_NONE) {
                if (UnloadUnusedExternalObjects()) {
                    KillTimer(TIMER_UNLOAD_UNUSED_EXTERNAL_OBJECTS);
                }
            }
        }
        break;
        case TIMER_HIDER:
            m_timerHider.NotifySubscribers();
            break;
        case TIMER_DELAYEDSEEK:
            KillTimer(TIMER_DELAYEDSEEK);
            if (queuedSeek.seekTime > 0) {
                SeekTo(queuedSeek.rtPos, queuedSeek.bShowOSD);
            }
            break;
        default:
            if (nIDEvent >= TIMER_ONETIME_START && nIDEvent <= TIMER_ONETIME_END) {
                m_timerOneTime.NotifySubscribers(nIDEvent);
            } else {
                ASSERT(FALSE);
            }
    }

    __super::OnTimer(nIDEvent);
}

LRESULT CMainFrame::OnDoStandby(WPARAM wParam, LPARAM lParam)
{
    if (GetLoadState() != MLS::CLOSED) {
        CloseMedia(false);
    }

    CAppSettings& s = AfxGetAppSettings(); 
    if (s.nCLSwitches & CLSW_STANDBY) {
        s.nCLSwitches ^= CLSW_STANDBY | CLSW_CLOSE;
    }     
    
    SetPrivilege(SE_SHUTDOWN_NAME);
    SetSystemPowerState(TRUE, FALSE);

    return S_OK;
}

LRESULT CMainFrame::OnDoHibernate(WPARAM wParam, LPARAM lParam)
{
    if (GetLoadState() != MLS::CLOSED) {
        CloseMedia(false);
    }

    CAppSettings& s = AfxGetAppSettings();
    if (s.nCLSwitches & CLSW_HIBERNATE) {
        s.nCLSwitches ^= CLSW_HIBERNATE | CLSW_CLOSE;
    }

    SetPrivilege(SE_SHUTDOWN_NAME);
    SetSystemPowerState(FALSE, FALSE);

    return S_OK;
}

LRESULT CMainFrame::OnDoShutdown(WPARAM wParam, LPARAM lParam)
{
    if (GetLoadState() != MLS::CLOSED) {
        CloseMedia(false);
    }

    SetPrivilege(SE_SHUTDOWN_NAME);
    InitiateSystemShutdownEx(nullptr, nullptr, 0, TRUE, FALSE, SHTDN_REASON_MAJOR_APPLICATION | SHTDN_REASON_MINOR_MAINTENANCE | SHTDN_REASON_FLAG_PLANNED);

    return S_OK;
}

LRESULT CMainFrame::OnDoLogOff(WPARAM wParam, LPARAM lParam)
{
    if (GetLoadState() != MLS::CLOSED) {
        CloseMedia(false);
    }

    SetPrivilege(SE_SHUTDOWN_NAME);
    ExitWindowsEx(EWX_LOGOFF | EWX_FORCEIFHUNG, 0);

    return S_OK;
}

LRESULT CMainFrame::OnDoOpenCurPlaylist(WPARAM wParam, LPARAM lParam)
{
    TRACE(L"OnDoOpenCurPlaylist\n");

    MSG msg;
    while (PeekMessage(&msg, nullptr, WM_MPC_OPENCURPLAYLIST, WM_MPC_OPENCURPLAYLIST, PM_REMOVE)) {
        TRACE(L"Dropping pending OpenCurPlaylist message\n");
    }

    if (!CloseMediaBeforeOpen()) {
        ASSERT(false);
#if !defined(_DEBUG) && USE_DRDUMP_CRASH_REPORTER && (MPC_VERSION_REV > 10)
        if (CrashReporter::IsEnabled()) {
            throw 1;
        }
#endif
        return S_OK;
    }

    bool reopen = (wParam == 1);
    OpenCurPlaylistItem(0, reopen);

    return S_OK;
}

void CMainFrame::DoAfterPlaybackEvent()
{
    CAppSettings& s = AfxGetAppSettings();
    bool bExitFullScreen = false;
    bool bNoMoreMedia = false;

    if (s.nCLSwitches & CLSW_DONOTHING) {
        // Do nothing
    } else if (s.nCLSwitches & CLSW_CLOSE) {
        SendMessage(WM_COMMAND, ID_FILE_EXIT);
    } else if (s.nCLSwitches & CLSW_MONITOROFF) {
        m_fEndOfStream = true;
        bExitFullScreen = true;
        SetThreadExecutionState(ES_CONTINUOUS);
        SendMessage(WM_SYSCOMMAND, SC_MONITORPOWER, 2);
    } else if (s.nCLSwitches & CLSW_STANDBY) {
        PostMessage(WM_MPC_STANDBY, 0, 0);
    } else if (s.nCLSwitches & CLSW_HIBERNATE) {
        PostMessage(WM_MPC_HIBERNATE, 0, 0);
    } else if (s.nCLSwitches & CLSW_SHUTDOWN) {
        PostMessage(WM_MPC_SHUTDOWN, 0, 0);
    } else if (s.nCLSwitches & CLSW_LOGOFF) {
        PostMessage(WM_MPC_LOGOFF, 0, 0);
    } else if (s.nCLSwitches & CLSW_LOCK) {
        m_fEndOfStream = true;
        bExitFullScreen = true;
        LockWorkStation();
    } else if (s.nCLSwitches & CLSW_PLAYNEXT) {
        if (SearchInDir(true, (s.fLoopForever || m_nLoops < s.nLoops || s.bLoopFolderOnPlayNextFile))) {
            PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
        } else {
            m_fEndOfStream = true;
            bExitFullScreen = true;
            bNoMoreMedia = true;
        }
    } else {
        // remembered after playback events
        switch (s.eAfterPlayback) {
            case CAppSettings::AfterPlayback::PLAY_NEXT:
                if (m_wndPlaylistBar.GetCount() < 2) { // ignore global PLAY_NEXT in case of a playlist
                    if (SearchInDir(true, s.bLoopFolderOnPlayNextFile)) {
                        PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
                    } else {
                        PostMessage(WM_COMMAND, ID_FILE_CLOSE_AND_RESTORE);
                    }
                }
                break;
            case CAppSettings::AfterPlayback::REWIND:
                bExitFullScreen = true;
                if (m_wndPlaylistBar.GetCount() > 1) {
                    s.nCLSwitches |= CLSW_OPEN;
                    PostMessage(WM_COMMAND, ID_NAVIGATE_SKIPFORWARD);
                } else {
                    SendMessage(WM_COMMAND, ID_PLAY_STOP);
                }
                break;
            case CAppSettings::AfterPlayback::MONITOROFF:
                m_fEndOfStream = true;
                bExitFullScreen = true;
                SetThreadExecutionState(ES_CONTINUOUS);
                PostMessage(WM_SYSCOMMAND, SC_MONITORPOWER, 2);
                break;
            case CAppSettings::AfterPlayback::CLOSE:
                PostMessage(WM_COMMAND, ID_FILE_CLOSE_AND_RESTORE);
                break;
            case CAppSettings::AfterPlayback::EXIT:
                if (GetLoadState() != MLS::CLOSED) {
                    PostMessage(WM_COMMAND, ID_FILE_EXIT);
                }
                break;
            default:
                m_fEndOfStream = true;
                bExitFullScreen = true;
                break;
        }
    }

    if (AfxGetMyApp()->m_fClosingState) {
        return;
    }

    if (m_fEndOfStream) {
        if (GetLoadState() == MLS::LOADED) {
            m_OSD.EnableShowMessage(false);
            SendMessage(WM_COMMAND, ID_PLAY_PAUSE);
            m_OSD.EnableShowMessage();
        }
        if (bNoMoreMedia) {
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_NO_MORE_MEDIA));
        }
    }

    if (bExitFullScreen && (IsFullScreenMode()) && s.fExitFullScreenAtTheEnd) {
        OnViewFullscreen();
    }
}

void CMainFrame::OnUpdateABRepeat(CCmdUI* pCmdUI) {
    bool canABRepeat = GetPlaybackMode() == PM_FILE || GetPlaybackMode() == PM_DVD;
    bool abRepeatActive = static_cast<bool>(abRepeat);

    switch (pCmdUI->m_nID) {
    case ID_PLAY_REPEAT_AB:
        pCmdUI->Enable(canABRepeat && abRepeatActive);
        break;
    case ID_PLAY_REPEAT_AB_MARK_A:
        if (pCmdUI->m_pMenu) {
            pCmdUI->m_pMenu->CheckMenuItem(ID_PLAY_REPEAT_AB_MARK_A, MF_BYCOMMAND | (abRepeat.positionA ? MF_CHECKED : MF_UNCHECKED));
        }
        pCmdUI->Enable(canABRepeat);
        break;
    case ID_PLAY_REPEAT_AB_MARK_B:
        if (pCmdUI->m_pMenu) {
            pCmdUI->m_pMenu->CheckMenuItem(ID_PLAY_REPEAT_AB_MARK_B, MF_BYCOMMAND | (abRepeat.positionB ? MF_CHECKED : MF_UNCHECKED));
        }
        pCmdUI->Enable(canABRepeat);
        break;
    default:
        ASSERT(FALSE);
        return;
    }
}


void CMainFrame::OnABRepeat(UINT nID) {
    switch (nID) {
    case ID_PLAY_REPEAT_AB:
        if (abRepeat) { //only support disabling from the menu
            DisableABRepeat();
        }
        break;
    case ID_PLAY_REPEAT_AB_MARK_A:
    case ID_PLAY_REPEAT_AB_MARK_B:
        REFERENCE_TIME rtDur = 0;
        int playmode = GetPlaybackMode();

        bool havePos = false;
        REFERENCE_TIME pos = 0;

        if (playmode == PM_FILE && m_pMS) {
            if (SUCCEEDED(m_pMS->GetDuration(&rtDur))) {
                havePos = SUCCEEDED(m_pMS->GetCurrentPosition(&pos)) && (rtDur >= pos);
            }
            if (!havePos && !abRepeat.positionA && !abRepeat.positionB) {
                return;
            }
        } else if (playmode == PM_DVD && m_pDVDI) {
            DVD_PLAYBACK_LOCATION2 Location;
            if (m_pDVDI->GetCurrentLocation(&Location) == S_OK) {
                double fps = Location.TimeCodeFlags == DVD_TC_FLAG_25fps ? 25.0
                    : Location.TimeCodeFlags == DVD_TC_FLAG_30fps ? 30.0
                    : Location.TimeCodeFlags == DVD_TC_FLAG_DropFrame ? 30 / 1.001
                    : 25.0;
                DVD_HMSF_TIMECODE tcDur;
                ULONG ulFlags;
                if (SUCCEEDED(m_pDVDI->GetTotalTitleTime(&tcDur, &ulFlags))) {
                    rtDur = HMSF2RT(tcDur, fps);
                }
                havePos = true;
                pos = HMSF2RT(Location.TimeCode, fps);
                abRepeat.dvdTitle = m_iDVDTitle; //we only support one title.  so if they clear or set, we will remember the current title
            }
        } else {
            return;
        }

        if (nID == ID_PLAY_REPEAT_AB_MARK_A) {
            if (abRepeat.positionA) {
                abRepeat.positionA = 0;
            } else if (havePos) {
                abRepeat.positionA = pos;
                if (abRepeat.positionB && (abRepeat.positionA >= abRepeat.positionB || !m_fShockwaveGraph && abRepeat.positionA + 500 * 10000LL > abRepeat.positionB)) {
                    abRepeat.positionB = 0;
                }
            }
        } else if (nID == ID_PLAY_REPEAT_AB_MARK_B) {
            if (abRepeat.positionB) {
                abRepeat.positionB = 0;
            } else if (havePos) {
                abRepeat.positionB = pos;
                if (m_fShockwaveGraph && abRepeat.positionB > abRepeat.positionA || abRepeat.positionB >= abRepeat.positionA + 500 * 10000LL) {
                    if (GetMediaState() == State_Running) {
                        PerformABRepeat(); //we just set loop point B, so we need to repeat right now
                    }
                } else {
                    abRepeat.positionB = 0;
                }
            }
        }

        auto pMRU = &AfxGetAppSettings().MRU;
        pMRU->UpdateCurrentABRepeat(abRepeat);

        m_wndSeekBar.Invalidate();
        break;
    }
}

void CMainFrame::PerformABRepeat() {
    if (!m_fShockwaveGraph) {
        ULONGLONG tcnow = GetTickCount64();
        if (tcnow > abRepeat.tcLastRepeat + 500ULL) {
            abRepeat.tcLastRepeat = tcnow;
        } else {
            // prevent endless loop
            DisableABRepeat();
            return;
        }
    }

    DoSeekTo(abRepeat.positionA, false);

    if (GetMediaState() == State_Stopped) {
        SendMessage(WM_COMMAND, ID_PLAY_PLAY);
    }
}

void CMainFrame::DisableABRepeat() {
    abRepeat = ABRepeat();

    auto* pMRU = &AfxGetAppSettings().MRU;
    pMRU->UpdateCurrentABRepeat(abRepeat);

    m_wndSeekBar.Invalidate();
}

bool CMainFrame::CheckABRepeat(REFERENCE_TIME& aPos, REFERENCE_TIME& bPos) {
    if (GetPlaybackMode() == PM_FILE || (GetPlaybackMode() == PM_DVD && m_iDVDTitle == abRepeat.dvdTitle)) {
        if (abRepeat) {
            aPos = abRepeat.positionA;
            bPos = abRepeat.positionB;
            return true;
        }
    }
    return false;
}


//
// graph event EC_COMPLETE handler
//
void CMainFrame::GraphEventComplete()
{
    CAppSettings& s = AfxGetAppSettings();

    auto* pMRU = &s.MRU;

    if (m_bRememberFilePos) {
        pMRU->UpdateCurrentFilePosition(0, true);
    }

    if (m_fFrameSteppingActive) {
        m_fFrameSteppingActive = false;
        m_nStepForwardCount = 0;
        MediaControlPause(true);
        if (m_pBA) {
            m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
        }
        m_fEndOfStream = true;
        return;
    }

    bool bBreak = false;
    if (m_wndPlaylistBar.IsAtEnd() || s.eLoopMode == CAppSettings::LoopMode::FILE) {
        ++m_nLoops;
        bBreak = !!(s.nCLSwitches & CLSW_AFTERPLAYBACK_MASK);
    }

    if (abRepeat) {
        PerformABRepeat();
    } else if (s.fLoopForever || m_nLoops < s.nLoops) {
        if (bBreak) {
            DoAfterPlaybackEvent();
        } else if ((m_wndPlaylistBar.GetCount() > 1) && (s.eLoopMode == CAppSettings::LoopMode::PLAYLIST)) {
            if (IsImageFile(lastOpenFile)) {
                REFERENCE_TIME rtDur = 0;
                if (!m_pMS || (m_pMS->GetDuration(&rtDur) != S_OK) || rtDur == 0) {
                    return; // no automatic jump to next file
                }
            }
            int nLoops = m_nLoops;
            SendMessage(WM_COMMAND, ID_NAVIGATE_SKIPFORWARDFILE);
            m_nLoops = nLoops;
        } else {
            if (GetMediaState() == State_Stopped) {
                SendMessage(WM_COMMAND, ID_PLAY_PLAY);
            } else if (m_pMS) {
                REFERENCE_TIME rtDur = 0;
                if ((m_pMS->GetDuration(&rtDur) == S_OK) && (rtDur >= 1000000LL) || !IsImageFile(lastOpenFile)) { // repeating still image is pointless and can cause player UI to freeze
                    REFERENCE_TIME rtPos = 0;
                    m_pMS->SetPositions(&rtPos, AM_SEEKING_AbsolutePositioning, nullptr, AM_SEEKING_NoPositioning);
                    if (GetMediaState() == State_Paused) {
                        SendMessage(WM_COMMAND, ID_PLAY_PLAY);
                    }
                }
            }
        }
    } else {
        DoAfterPlaybackEvent();
    }
}

//
// our WM_GRAPHNOTIFY handler
//

LRESULT CMainFrame::OnGraphNotify(WPARAM wParam, LPARAM lParam)
{
    if (wParam != 0) {
        ASSERT(false);
        return S_OK;
    }
    if (AfxGetMyApp()->m_fClosingState) {
        ASSERT(false);
        return S_OK;
    }

    MLS loadstate;
    {
        CAutoLock ga(&lockGraphAccess);
        if (AfxGetMyApp()->m_fClosingState || m_fOpeningAborted || !m_pME || lParam != (LPARAM)m_pME.p) {
            ASSERT(false);
            return S_OK;
        }
        loadstate = m_eMediaLoadState;
        if (loadstate != MLS::LOADED && loadstate != MLS::LOADING) {
            ASSERT(false);
            return S_OK;
        }
    }

    HRESULT hr = S_OK;
    LONG evCode = 0;
    LONG_PTR evParam1, evParam2;
    // there should be WM_GRAPHNOTIFY message for each event, so no need for a loop here
    if (SUCCEEDED(m_pME->GetEvent(&evCode, &evParam1, &evParam2, 0))) {
        m_ActiveGraphNotifyEvCode = evCode;
#ifdef _DEBUG
        if (evCode != EC_DVD_CURRENT_HMSF_TIME) {
            TRACE(_T("--> CMainFrame::OnGraphNotify (thread %lu)(graph %u)(loadstate %d) event: %ws\n"), GetCurrentThreadId(), (unsigned int)(lParam & 0xffff), loadstate, GetEventString(evCode));
        }
#else
        if (evCode != EC_DVD_CURRENT_HMSF_TIME && USE_LOGGER(AfxGetAppSettings())) {
            PLAYER_LOG(_T("CMainFrame::OnGraphNotify (thread %lu)(graph %u)(loadstate %d) event: %ws"), GetCurrentThreadId(), (unsigned int)(lParam & 0xffff), loadstate, GetEventString(evCode));
        }
#endif

        CString str;
        if (m_fCustomGraph) {
            if (EC_BG_ERROR == evCode) {
                str = CString((char*)evParam1);
            }
        }
        hr = m_pME->FreeEventParams(evCode, evParam1, evParam2);

        switch (evCode) {
            case EC_PAUSED:
                if (loadstate == MLS::LOADED) {
                    UpdateCachedMediaState();
                    if (m_audioTrackCount > 1) {
                        CheckSelectedAudioStream();
                    }
                }
                break;
            case EC_COMPLETE:
                UpdateCachedMediaState();
                GraphEventComplete();
                break;
            case EC_ERRORABORT:
                UpdateCachedMediaState();
                TRACE(_T("\thr = %08x\n"), (HRESULT)evParam1);
                break;
            case EC_BUFFERING_DATA:
                TRACE(_T("\tBuffering data = %s\n"), evParam1 ? _T("true") : _T("false"));
                m_bBuffering = !!evParam1;
                break;
            case EC_STEP_COMPLETE:
                if (m_fFrameSteppingActive) {
                    m_nStepForwardCount++;
                }
                UpdateCachedMediaState();
                break;
            case EC_DEVICE_LOST:
                UpdateCachedMediaState();
                if (evParam2 == 0) {
                    // Device lost
                    if (GetPlaybackMode() == PM_ANALOG_CAPTURE) {
                        CComQIPtr<IBaseFilter> pBF = (IUnknown*)evParam1;
                        if (!m_pVidCap && m_pVidCap == pBF || !m_pAudCap && m_pAudCap == pBF) {
                            SendMessage(WM_COMMAND, ID_FILE_CLOSE_AND_RESTORE);
                        }
                    } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
                        SendMessage(WM_COMMAND, ID_FILE_CLOSE_AND_RESTORE);
                    }
                }
                break;
            case EC_STREAM_ERROR_STILLPLAYING:
            case EC_STREAM_ERROR_STOPPED:
                TRACE(L"Failure code %x %x\n", evParam1, evParam2);
                break;
            case EC_DVD_TITLE_CHANGE: {
                if (GetPlaybackMode() == PM_FILE) {
                    SetupChapters();
                } else if (GetPlaybackMode() == PM_DVD) {
                    m_iDVDTitle = (DWORD)evParam1;

                    if (m_iDVDDomain == DVD_DOMAIN_Title) {
                        CString Domain;
                        Domain.Format(IDS_AG_TITLE, m_iDVDTitle);
                        m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_DOMAIN), Domain);
                    }

                    SetupDVDChapters();
                }
                SetupSubtitlesSubMenu();
                SetupAudioSubMenu();
            }
            break;
            case EC_DVD_DOMAIN_CHANGE: {
                CAppSettings& s = AfxGetAppSettings();
                m_iDVDDomain = (DVD_DOMAIN)evParam1;

                OpenDVDData* pDVDData = dynamic_cast<OpenDVDData*>(m_lastOMD.m_p);
                ASSERT(pDVDData);

                CString Domain(_T('-'));

                switch (m_iDVDDomain) {
                    case DVD_DOMAIN_FirstPlay:
                        ULONGLONG llDVDGuid;

                        Domain = _T("First Play");

                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }

                        if (m_pDVDI && SUCCEEDED(m_pDVDI->GetDiscID(nullptr, &llDVDGuid))) {
                            m_fValidDVDOpen = true;

                            if (s.fShowDebugInfo) {
                                m_OSD.DebugMessage(_T("DVD Title: %lu"), s.lDVDTitle);
                            }

                            if (s.lDVDTitle != 0) {
                                // Set command line position
                                hr = m_pDVDC->PlayTitle(s.lDVDTitle, DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                if (s.fShowDebugInfo) {
                                    m_OSD.DebugMessage(_T("PlayTitle: 0x%08X"), hr);
                                    m_OSD.DebugMessage(_T("DVD Chapter: %lu"), s.lDVDChapter);
                                }

                                if (s.lDVDChapter > 1) {
                                    hr = m_pDVDC->PlayChapterInTitle(s.lDVDTitle, s.lDVDChapter, DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                    if (s.fShowDebugInfo) {
                                        m_OSD.DebugMessage(_T("PlayChapterInTitle: 0x%08X"), hr);
                                    }
                                } else {
                                    // Trick: skip trailers with some DVDs
                                    hr = m_pDVDC->Resume(DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                    if (s.fShowDebugInfo) {
                                        m_OSD.DebugMessage(_T("Resume: 0x%08X"), hr);
                                    }

                                    // If the resume call succeeded, then we skip PlayChapterInTitle
                                    // and PlayAtTimeInTitle.
                                    if (hr == S_OK) {
                                        // This might fail if the Title is not available yet?
                                        hr = m_pDVDC->PlayAtTime(&s.DVDPosition,
                                                                 DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                        if (s.fShowDebugInfo) {
                                            m_OSD.DebugMessage(_T("PlayAtTime: 0x%08X"), hr);
                                        }
                                    } else {
                                        if (s.fShowDebugInfo)
                                            m_OSD.DebugMessage(_T("Timecode requested: %02d:%02d:%02d.%03d"),
                                                               s.DVDPosition.bHours, s.DVDPosition.bMinutes,
                                                               s.DVDPosition.bSeconds, s.DVDPosition.bFrames);

                                        // Always play chapter 1 (for now, until something else dumb happens)
                                        hr = m_pDVDC->PlayChapterInTitle(s.lDVDTitle, 1,
                                                                         DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                        if (s.fShowDebugInfo) {
                                            m_OSD.DebugMessage(_T("PlayChapterInTitle: 0x%08X"), hr);
                                        }

                                        // This might fail if the Title is not available yet?
                                        hr = m_pDVDC->PlayAtTime(&s.DVDPosition,
                                                                 DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                        if (s.fShowDebugInfo) {
                                            m_OSD.DebugMessage(_T("PlayAtTime: 0x%08X"), hr);
                                        }

                                        if (hr != S_OK) {
                                            hr = m_pDVDC->PlayAtTimeInTitle(s.lDVDTitle, &s.DVDPosition,
                                                                            DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                            if (s.fShowDebugInfo) {
                                                m_OSD.DebugMessage(_T("PlayAtTimeInTitle: 0x%08X"), hr);
                                            }
                                        }
                                    } // Resume

                                    hr = m_pDVDC->PlayAtTime(&s.DVDPosition,
                                                             DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                    if (s.fShowDebugInfo) {
                                        m_OSD.DebugMessage(_T("PlayAtTime: %d"), hr);
                                    }
                                }

                                m_iDVDTitle   = s.lDVDTitle;
                                s.lDVDTitle   = 0;
                                s.lDVDChapter = 0;
                            } else if (pDVDData && pDVDData->pDvdState) {
                                // Set position from favorite
                                VERIFY(SUCCEEDED(m_pDVDC->SetState(pDVDData->pDvdState, DVD_CMD_FLAG_Block, nullptr)));
                                // We don't want to restore the position from the favorite
                                // if the playback is reinitialized so we clear the saved state
                                pDVDData->pDvdState.Release();
                            } else if (s.fKeepHistory && s.fRememberDVDPos && s.MRU.GetCurrentDVDPosition().llDVDGuid) {
                                // Set last remembered position (if found...)
                                DVD_POSITION dvdPosition = s.MRU.GetCurrentDVDPosition();

                                hr = m_pDVDC->PlayTitle(dvdPosition.lTitle, DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                if (FAILED(hr)) {
                                    TRACE(_T("Failed to set remembered DVD title index, hr = 0x%08X"), hr);
                                } else {
                                    m_iDVDTitle = dvdPosition.lTitle;

                                    if (dvdPosition.timecode.bSeconds > 0 || dvdPosition.timecode.bMinutes > 0 || dvdPosition.timecode.bHours > 0 || dvdPosition.timecode.bFrames > 0) {
#if 0
                                        hr = m_pDVDC->Resume(DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                                        if (FAILED(hr)) {
                                            TRACE(_T("Failed to set remembered DVD resume flags, hr = 0x%08X"), hr);
                                        }
#endif
#if 0
                                        hr = m_pDVDC->PlayAtTimeInTitle(dvdPosition.lTitle, &dvdPosition.timecode, DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
#else
                                        hr = m_pDVDC->PlayAtTime(&dvdPosition.timecode, DVD_CMD_FLAG_Flush, nullptr);
#endif
                                    }

                                    ABRepeat tmp = s.MRU.GetCurrentABRepeat();
                                    if (tmp.dvdTitle == m_iDVDTitle) {
                                        abRepeat = tmp;
                                        m_wndSeekBar.Invalidate();
                                    }
                                }
                            }

                            if (s.fRememberZoomLevel && !IsFullScreenMode() && !IsZoomed() && !IsIconic() && !IsAeroSnapped()) { // Hack to the normal initial zoom for DVD + DXVA ...
                                ZoomVideoWindow();
                            }
                        }
                        break;
                    case DVD_DOMAIN_VideoManagerMenu:
                        Domain = _T("Video Manager Menu");
                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }
                        break;
                    case DVD_DOMAIN_VideoTitleSetMenu:
                        Domain = _T("Video Title Set Menu");
                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }
                        break;
                    case DVD_DOMAIN_Title:
                        Domain.Format(IDS_AG_TITLE, m_iDVDTitle);
                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }
                        if (s.fKeepHistory && s.fRememberDVDPos) {
                            s.MRU.UpdateCurrentDVDTitle(m_iDVDTitle);
                        }
                        if (!m_fValidDVDOpen && m_pDVDC) {
                            m_fValidDVDOpen = true;
                            m_pDVDC->ShowMenu(DVD_MENU_Title, DVD_CMD_FLAG_Block | DVD_CMD_FLAG_Flush, nullptr);
                        }
                        break;
                    case DVD_DOMAIN_Stop:
                        Domain.LoadString(IDS_AG_STOP);
                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }
                        break;
                    default:
                        Domain = _T("-");
                        if (s.fShowDebugInfo) {
                            m_OSD.DebugMessage(_T("%s"), Domain.GetString());
                        }
                        break;
                }

                m_wndInfoBar.SetLine(StrRes(IDS_INFOBAR_DOMAIN), Domain);

                if (GetPlaybackMode() == PM_FILE) {
                    SetupChapters();
                } else if (GetPlaybackMode() == PM_DVD) {
                    SetupDVDChapters();
                }

#if 0   // UOPs debug traces
                if (hr == VFW_E_DVD_OPERATION_INHIBITED) {
                    ULONG UOPfields = 0;
                    pDVDI->GetCurrentUOPS(&UOPfields);
                    CString message;
                    message.Format(_T("UOP bitfield: 0x%08X; domain: %s"), UOPfields, Domain);
                    m_OSD.DisplayMessage(OSD_TOPLEFT, message);
                } else {
                    m_OSD.DisplayMessage(OSD_TOPRIGHT, Domain);
                }
#endif

                MoveVideoWindow(); // AR might have changed
            }
            break;
            case EC_DVD_CURRENT_HMSF_TIME: {
                CAppSettings& s = AfxGetAppSettings();
                s.MRU.UpdateCurrentDVDTimecode((DVD_HMSF_TIMECODE*)&evParam1);
            }
            break;
            case EC_DVD_ERROR: {
                TRACE(_T("\t%I64d %Id\n"), evParam1, evParam2);

                UINT err;

                switch (evParam1) {
                    case DVD_ERROR_Unexpected:
                    default:
                        err = IDS_MAINFRM_16;
                        break;
                    case DVD_ERROR_CopyProtectFail:
                        err = IDS_MAINFRM_17;
                        break;
                    case DVD_ERROR_InvalidDVD1_0Disc:
                        err = IDS_MAINFRM_18;
                        break;
                    case DVD_ERROR_InvalidDiscRegion:
                        err = IDS_MAINFRM_19;
                        break;
                    case DVD_ERROR_LowParentalLevel:
                        err = IDS_MAINFRM_20;
                        break;
                    case DVD_ERROR_MacrovisionFail:
                        err = IDS_MAINFRM_21;
                        break;
                    case DVD_ERROR_IncompatibleSystemAndDecoderRegions:
                        err = IDS_MAINFRM_22;
                        break;
                    case DVD_ERROR_IncompatibleDiscAndDecoderRegions:
                        err = IDS_MAINFRM_23;
                        break;
                }

                SendMessage(WM_COMMAND, ID_FILE_CLOSEMEDIA);

                SetClosingError(err);
            }
            break;
            case EC_DVD_WARNING:
                TRACE(_T("\t%Id %Id\n"), evParam1, evParam2);
                break;
            case EC_VIDEO_SIZE_CHANGED: {
                CSize size(LOWORD(evParam1), HIWORD(evParam1));
                TRACE(_T("\t%ldx%ld\n"), size.cx, size.cy);
                const bool bWasAudioOnly = m_fAudioOnly;
                m_fAudioOnly = (size.cx <= 0 || size.cy <= 0);
                OnVideoSizeChanged(bWasAudioOnly);
                m_statusbarVideoSize.Format(_T("%dx%d"), size.cx, size.cy);
                if (loadstate == MLS::LOADED) {
                    UpdateDXVAStatus();
                    CheckSelectedVideoStream();
                }
            }
            break;
            case EC_LENGTH_CHANGED: {
                REFERENCE_TIME rtDur = 0;
                m_pMS->GetDuration(&rtDur);
                m_wndPlaylistBar.SetCurTime(rtDur);
                OnTimer(TIMER_STREAMPOSPOLLER);
                OnTimer(TIMER_STREAMPOSPOLLER2);
                LoadKeyFrames();
                if (GetPlaybackMode() == PM_FILE) {
                    SetupChapters();
                    if (m_bUseSeekPreview) {
                        SyncPreviewEdition();
                    }
                } else if (GetPlaybackMode() == PM_DVD) {
                    SetupDVDChapters();
                }
            }
            break;
            case EC_BG_AUDIO_CHANGED:
                if (m_fCustomGraph) {
                    int nAudioChannels = (int)evParam1;

                    m_wndStatusBar.SetStatusBitmap(nAudioChannels == 1 ? IDB_AUDIOTYPE_MONO
                                                   : nAudioChannels >= 2 ? IDB_AUDIOTYPE_STEREO
                                                   : IDB_AUDIOTYPE_NOAUDIO);
                }
                break;
            case EC_BG_ERROR:
                if (m_fCustomGraph) {
                    SendMessage(WM_COMMAND, ID_FILE_CLOSEMEDIA);
                    SetClosingError(!str.IsEmpty() ? str : CString(_T("Unspecified graph error")));
                    m_wndPlaylistBar.SetCurValid(false);
                }
                break;
            case EC_DVD_PLAYBACK_RATE_CHANGE:
                if (m_fCustomGraph) {
                    CAppSettings& s = AfxGetAppSettings();
                    if (s.autoChangeFSMode.bEnabled && IsFullScreenMode() && m_iDVDDomain == DVD_DOMAIN_Title) {
                        AutoChangeMonitorMode();
                    }
                }
                break;
            case EC_CLOCK_CHANGED:
                /*
                if (m_pBA && !m_fFrameSteppingActive) {
                    m_pBA->put_Volume(m_wndToolBar.Volume);
                }
                */
                break;
            case 0xfa17:
                // madVR changed graph state
                UpdateCachedMediaState();
                break;
            case EC_DVD_STILL_ON:
                m_bDVDStillOn = true;
                break;
            case EC_DVD_STILL_OFF:
                m_bDVDStillOn = false;
                break;
            case EC_DVD_BUTTON_CHANGE:
            case EC_DVD_SUBPICTURE_STREAM_CHANGE:
            case EC_DVD_AUDIO_STREAM_CHANGE:
            case EC_DVD_ANGLE_CHANGE:
            case EC_DVD_VALID_UOPS_CHANGE:
            case EC_DVD_CHAPTER_START:
                // no action required
                break;
            default:
                UpdateCachedMediaState();
                TRACE(_T("Unhandled graph event\n"));
        }
    }

    m_ActiveGraphNotifyEvCode = 0;
    return hr;
}

LRESULT CMainFrame::OnResetDevice(WPARAM wParam, LPARAM lParam)
{
    if (!IsStateLoaded()) {
        return S_OK;
    }

    m_OSD.HideMessage(true);

    OAFilterState fs = GetMediaState();
    if (fs == State_Running) {
        if (!IsPlaybackCaptureMode()) {
            MediaControlPause(true);
        } else {
            MediaControlStop(true); // Capture mode doesn't support pause
        }
    }

    if (m_bOpenedThroughThread && m_pGraphThread && m_pGraphThread->m_hThread) {
        CAMMsgEvent e;
        if (m_pGraphThread->PostThreadMessage(CGraphThread::TM_RESET, (WPARAM)0, (LPARAM)&e)) {
            e.WaitMsg();
        } else {
            ResetDevice();
        }
    } else {
        ResetDevice();
    }

    if (fs == State_Running && m_pMC) {
        MediaControlRun();        

        // When restarting DVB capture, we need to set again the channel.
        if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
            CComQIPtr<IBDATuner> pTun = m_pGB;
            if (pTun) {
                SetChannel(AfxGetAppSettings().nDVBLastChannel);
            }
        }
    }

    if (m_OSD.CanShowMessage()) {
        m_OSD.HideMessage(false);
    }

    return S_OK;
}

LRESULT CMainFrame::OnRepaintRenderLess(WPARAM wParam, LPARAM lParam)
{
    MoveVideoWindow();
    return TRUE;
}

void CMainFrame::SaveAppSettings()
{
    MSG msg;
    if (!PeekMessage(&msg, m_hWnd, WM_SAVESETTINGS, WM_SAVESETTINGS, PM_NOREMOVE | PM_NOYIELD)) {
        AfxGetAppSettings().SaveSettings();
    }
}

LRESULT CMainFrame::OnNcHitTest(CPoint point)
{
    LRESULT nHitTest = __super::OnNcHitTest(point);
    return ((IsCaptionHidden()) && nHitTest == HTCLIENT) ? HTCAPTION : nHitTest;
}

void CMainFrame::OnHScroll(UINT nSBCode, UINT nPos, CScrollBar* pScrollBar)
{
    // pScrollBar is null when making horizontal scroll with pen tablet
    if (!pScrollBar) return;
    
    if (pScrollBar->IsKindOf(RUNTIME_CLASS(CVolumeCtrl))) {
        OnPlayVolume(0);
    } else if (pScrollBar->IsKindOf(RUNTIME_CLASS(CPlayerSeekBar)) && GetLoadState() == MLS::LOADED) {
        SeekTo(m_wndSeekBar.GetPos());
    } else if (*pScrollBar == *m_pVideoWnd) {
        SeekTo(m_OSD.GetPos());
    }

    __super::OnHScroll(nSBCode, nPos, pScrollBar);
}

void CMainFrame::RestoreFocus() {
    CWnd* curFocus = GetFocus();
    if (curFocus && curFocus != this) {
        SetFocus();
    }
}

void CMainFrame::OnInitMenu(CMenu* pMenu)
{
    __super::OnInitMenu(pMenu);
    RestoreFocus();

    const UINT uiMenuCount = pMenu->GetMenuItemCount();
    if (uiMenuCount == -1) {
        return;
    }

    MENUITEMINFO mii;
    mii.cbSize = sizeof(mii);

    for (UINT i = 0; i < uiMenuCount; ++i) {
#ifdef _DEBUG
        CString str;
        pMenu->GetMenuString(i, str, MF_BYPOSITION);
        str.Remove('&');
#endif
        UINT itemID = pMenu->GetMenuItemID(i);
        if (itemID == 0xFFFFFFFF) {
            mii.fMask = MIIM_ID;
            pMenu->GetMenuItemInfo(i, &mii, TRUE);
            itemID = mii.wID;
        }

        CMPCThemeMenu* pSubMenu = nullptr;

        if (itemID == ID_FAVORITES) {
            SetupFavoritesSubMenu();
            pSubMenu = &m_favoritesMenu;
        }/*else if (itemID == ID_RECENT_FILES) {
            SetupRecentFilesSubMenu();
            pSubMenu = &m_recentFilesMenu;
        }*/

        if (pSubMenu) {
            mii.fMask = MIIM_STATE | MIIM_SUBMENU;
            mii.fState = (pSubMenu->GetMenuItemCount()) > 0 ? MFS_ENABLED : MFS_DISABLED;
            mii.hSubMenu = *pSubMenu;
            VERIFY(CMPCThemeMenu::SetThemedMenuItemInfo(pMenu, i, &mii, TRUE));
            pSubMenu->fulfillThemeReqs();
        }
    }
}

void CMainFrame::OnInitMenuPopup(CMenu* pPopupMenu, UINT nIndex, BOOL bSysMenu) {
    __super::OnInitMenuPopup(pPopupMenu, nIndex, bSysMenu);

    if (bSysMenu) {
        m_pActiveSystemMenu = pPopupMenu;
        m_eventc.FireEvent(MpcEvent::SYSTEM_MENU_POPUP_INITIALIZED);
        return;
    }

    UINT uiMenuCount = pPopupMenu->GetMenuItemCount();
    if (uiMenuCount == -1) {
        return;
    }

    MENUITEMINFO mii;
    mii.cbSize = sizeof(mii);

    for (UINT i = 0; i < uiMenuCount; ++i) {
#ifdef _DEBUG
        CString str;
        pPopupMenu->GetMenuString(i, str, MF_BYPOSITION);
        str.Remove('&');
#endif
        UINT firstSubItemID = 0;
        CMenu* sm = pPopupMenu->GetSubMenu(i);
        if (sm) {
            firstSubItemID = sm->GetMenuItemID(0);
        }

        if (firstSubItemID == ID_NAVIGATE_SKIPBACK) { // is "Navigate" submenu {
            UINT fState = (GetLoadState() == MLS::LOADED
                && (1/*GetPlaybackMode() == PM_DVD *//*|| (GetPlaybackMode() == PM_FILE && !m_PlayList.IsEmpty())*/))
                ? MF_ENABLED
                : MF_GRAYED;
            pPopupMenu->EnableMenuItem(i, MF_BYPOSITION | fState);
            continue;
        }
        if (firstSubItemID == ID_VIEW_VF_HALF               // is "Video Frame" submenu
            || firstSubItemID == ID_VIEW_INCSIZE        // is "Pan&Scan" submenu
            || firstSubItemID == ID_ASPECTRATIO_START   // is "Override Aspect Ratio" submenu
            || firstSubItemID == ID_VIEW_ZOOM_25) {     // is "Zoom" submenu
            UINT fState = (GetLoadState() == MLS::LOADED && !m_fAudioOnly)
                ? MF_ENABLED
                : MF_GRAYED;
            pPopupMenu->EnableMenuItem(i, MF_BYPOSITION | fState);
            continue;
        }

        // "File -> Subtitles" submenu
        if (firstSubItemID == ID_FILE_SUBTITLES_LOAD) {
            UINT fState = (GetLoadState() == MLS::LOADED && !m_fAudioOnly && m_pCAP)
                ? MF_ENABLED
                : MF_GRAYED;
            pPopupMenu->EnableMenuItem(i, MF_BYPOSITION | fState);
            continue;
        }

        // renderer settings
        if (firstSubItemID == ID_VIEW_TEARING_TEST) {
            UINT fState = MF_GRAYED;
            const CAppSettings& s = AfxGetAppSettings();
            if (s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM || s.iDSVideoRendererType == VIDRNDT_DS_SYNC || s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS) {
                fState = MF_ENABLED;
            }
            pPopupMenu->EnableMenuItem(i, MF_BYPOSITION | fState);
            continue;
        }

        UINT itemID = pPopupMenu->GetMenuItemID(i);
        if (itemID == 0xFFFFFFFF) {
            mii.fMask = MIIM_ID;
            VERIFY(pPopupMenu->GetMenuItemInfo(i, &mii, TRUE));
            itemID = mii.wID;
        }
        CMPCThemeMenu* pSubMenu = nullptr;

        // debug shaders
        if (itemID == ID_VIEW_DEBUGSHADERS) {
            UINT fState = MF_GRAYED;
            if (GetLoadState() == MLS::LOADED && !m_fAudioOnly && m_pCAP2) {
                fState = MF_ENABLED;
            }
            pPopupMenu->EnableMenuItem(i, MF_BYPOSITION | fState);
            continue;
        }

        if (itemID == ID_FILE_OPENDISC) {
            SetupOpenCDSubMenu();
            pSubMenu = &m_openCDsMenu;
        } else if (itemID == ID_FILTERS) {
            SetupFiltersSubMenu();
            pSubMenu = &m_filtersMenu;
        } else if (itemID == ID_AUDIOS) {
            SetupAudioSubMenu();
            pSubMenu = &m_audiosMenu;
        } else if (itemID == ID_SUBTITLES) {
            SetupSubtitlesSubMenu();
            pSubMenu = &m_subtitlesMenu;
        } else if (itemID == ID_SUBTITLES_SECONDARY) {
            SetupSecondarySubtitleSubMenu();
            pSubMenu = &m_subtitlesSecondaryMenu;
        } else if (itemID == ID_VIDEO_STREAMS) {
            CString menuStr;
            menuStr.LoadString(GetPlaybackMode() == PM_DVD ? IDS_MENU_VIDEO_ANGLE : IDS_MENU_VIDEO_STREAM);

            mii.fMask = MIIM_STRING;
            mii.dwTypeData = (LPTSTR)(LPCTSTR)menuStr;
            VERIFY(CMPCThemeMenu::SetThemedMenuItemInfo(pPopupMenu, i, &mii, TRUE));

            SetupVideoStreamsSubMenu();
            pSubMenu = &m_videoStreamsMenu;
        } else if (itemID == ID_NAVIGATE_GOTO) {
            // ID_NAVIGATE_GOTO is just a marker we use to insert the appropriate submenus
            SetupJumpToSubMenus(pPopupMenu, i + 1);
            uiMenuCount = pPopupMenu->GetMenuItemCount(); //SetupJumpToSubMenus could actually reduce the menu count!
        } else if (itemID == ID_FAVORITES) {
            SetupFavoritesSubMenu();
            pSubMenu = &m_favoritesMenu;
        } else if (itemID == ID_RECENT_FILES) {
            SetupRecentFilesSubMenu();
            pSubMenu = &m_recentFilesMenu;
        } else if (itemID == ID_SHADERS) {
            if (SetupShadersSubMenu()) {
                pPopupMenu->EnableMenuItem(ID_SHADERS, MF_BYPOSITION | MF_ENABLED);
            } else {
                pPopupMenu->EnableMenuItem(ID_SHADERS, MF_BYPOSITION | MF_GRAYED);
            }
            pSubMenu = &m_shadersMenu;
        }

        if (pSubMenu) {
            mii.fMask = MIIM_STATE | MIIM_SUBMENU;
            mii.fState = (pSubMenu->GetMenuItemCount() > 0) ? MF_ENABLED : MF_GRAYED;
            mii.hSubMenu = *pSubMenu;
            VERIFY(CMPCThemeMenu::SetThemedMenuItemInfo(pPopupMenu, i, &mii, TRUE));
            pSubMenu->fulfillThemeReqs();
        }
    }

    uiMenuCount = pPopupMenu->GetMenuItemCount();
    if (uiMenuCount == -1) {
        return;
    }

    if (!AppIsThemeLoaded()) { //themed menus draw accelerators already, no need to append
        for (UINT i = 0; i < uiMenuCount; ++i) {
            UINT nID = pPopupMenu->GetMenuItemID(i);
            //the dynamically named items not listed here (filters, shader presets, favorite discs, optical drives)
            //have no accelerator, so the key.IsEmpty() && k < 0 test below already skips them
            if (nID == ID_SEPARATOR || nID == -1
                || nID >= ID_FAVORITES_FILE_START && nID <= ID_FAVORITES_FILE_END
                || nID >= ID_RECENT_FILE_START && nID <= ID_RECENT_FILE_END
                || nID >= ID_SUBTITLES_SUBITEM_START && nID <= ID_SUBTITLES_SUBITEM_END
                || nID >= ID_SUBTITLES_SECONDARY_SUBITEM_START && nID <= ID_SUBTITLES_SECONDARY_SUBITEM_END
                || nID >= ID_NAVIGATE_JUMPTO_SUBITEM_START && nID <= ID_NAVIGATE_JUMPTO_SUBITEM_END) {
                continue;
            }

            CString str;
            pPopupMenu->GetMenuString(i, str, MF_BYPOSITION);
            int k = str.Find('\t');
            if (k > 0) {
                str = str.Left(k);
            }

            CString key = CPPageAccelTbl::MakeAccelShortcutLabel(nID);
            if (key.IsEmpty() && k < 0) {
                continue;
            }
            str += _T("\t") + key;

            // BUG(?): this disables menu item update ui calls for some reason...
            //pPopupMenu->ModifyMenu(i, MF_BYPOSITION|MF_STRING, nID, str);

            // this works fine
            mii.fMask = MIIM_STRING;
            mii.dwTypeData = (LPTSTR)(LPCTSTR)str;
            VERIFY(pPopupMenu->SetMenuItemInfo(i, &mii, TRUE));
        }
    }

    uiMenuCount = pPopupMenu->GetMenuItemCount();
    if (uiMenuCount == -1) {
        return;
    }

    bool fPnSPresets = false;

    for (UINT i = 0; i < uiMenuCount; ++i) {
        UINT nID = pPopupMenu->GetMenuItemID(i);

        if (nID >= ID_PANNSCAN_PRESETS_START && nID < ID_PANNSCAN_PRESETS_END) {
            do {
                nID = pPopupMenu->GetMenuItemID(i);
                VERIFY(pPopupMenu->DeleteMenu(i, MF_BYPOSITION));
                uiMenuCount--;
            } while (i < uiMenuCount && nID >= ID_PANNSCAN_PRESETS_START && nID < ID_PANNSCAN_PRESETS_END);

            nID = pPopupMenu->GetMenuItemID(i);
        }

        if (nID == ID_VIEW_RESET) {
            fPnSPresets = true;
        }
    }

    if (fPnSPresets) {
        bool usetheme = AppIsThemeLoaded();
        const CAppSettings& s = AfxGetAppSettings();
        INT_PTR i = 0, j = s.m_pnspresets.GetCount();
        for (; i < j; i++) {
            int k = 0;
            CString label = SanitizeMenuLabel(s.m_pnspresets[i].Tokenize(_T(","), k));
            VERIFY(pPopupMenu->InsertMenu(ID_VIEW_RESET, MF_BYCOMMAND, ID_PANNSCAN_PRESETS_START + i, label));
            CMPCThemeMenu::fulfillThemeReqsItem(pPopupMenu, (UINT)(ID_PANNSCAN_PRESETS_START + i), true);
        }
        //if (j > 0)
        {
            VERIFY(pPopupMenu->InsertMenu(ID_VIEW_RESET, MF_BYCOMMAND, ID_PANNSCAN_PRESETS_START + i, ResStr(IDS_PANSCAN_EDIT)));
            VERIFY(pPopupMenu->InsertMenu(ID_VIEW_RESET, MF_BYCOMMAND | MF_SEPARATOR));
            if (usetheme) {
                CMPCThemeMenu::fulfillThemeReqsItem(pPopupMenu, (UINT)(ID_PANNSCAN_PRESETS_START + i), true);
                UINT pos = CMPCThemeMenu::getPosFromID(pPopupMenu, ID_VIEW_RESET); //separator is inserted right before view_reset
                CMPCThemeMenu::fulfillThemeReqsItem(pPopupMenu, pos - 1);
            }
        }
    }

    if (m_pActiveContextMenu == pPopupMenu) {
        m_eventc.FireEvent(MpcEvent::CONTEXT_MENU_POPUP_INITIALIZED);
    }
}

void CMainFrame::OnUnInitMenuPopup(CMenu* pPopupMenu, UINT nFlags)
{
    __super::OnUnInitMenuPopup(pPopupMenu, nFlags);
    if (m_pActiveContextMenu == pPopupMenu) {
        m_pActiveContextMenu = nullptr;
        m_eventc.FireEvent(MpcEvent::CONTEXT_MENU_POPUP_UNINITIALIZED);
    } else if (m_pActiveSystemMenu == pPopupMenu) {
        m_pActiveSystemMenu = nullptr;
        SendMessage(WM_CANCELMODE); // unfocus main menu if system menu was entered with alt+space
        m_eventc.FireEvent(MpcEvent::SYSTEM_MENU_POPUP_UNINITIALIZED);
    }
}

void CMainFrame::OnEnterMenuLoop(BOOL bIsTrackPopupMenu)
{
    if (!bIsTrackPopupMenu && !m_pActiveSystemMenu && GetMenuBarState() == AFX_MBS_HIDDEN) {
        // mfc has problems synchronizing menu visibility with modal loop in certain situations
        ASSERT(!m_pActiveContextMenu);
        VERIFY(SetMenuBarState(AFX_MBS_VISIBLE));
    }
    __super::OnEnterMenuLoop(bIsTrackPopupMenu);
}

BOOL CMainFrame::OnQueryEndSession()
{
    return TRUE;
}

void CMainFrame::OnEndSession(BOOL bEnding)
{
    // do nothing for now
}

BOOL CMainFrame::OnMenu(CMenu* pMenu)
{
    if (!pMenu) {
        return FALSE;
    }

    CPoint point;
    GetCursorPos(&point);

    // Do not show popup menu in D3D fullscreen it has several adverse effects.
    if (IsD3DFullScreenMode()) {
        CWnd* pWnd = WindowFromPoint(point);
        if (pWnd && *pWnd == *m_pDedicatedFSVideoWnd) {
            return FALSE;
        }
    }

    if (AfxGetMyApp()->m_fClosingState) {
        return FALSE; //prevent crash when player closes with context menu open
    }

    m_pActiveContextMenu = pMenu;

    pMenu->TrackPopupMenu(TPM_RIGHTBUTTON | TPM_NOANIMATION, point.x, point.y, this);

    return TRUE;
}

CMPCThemeMenu* CMainFrame::GetShortMenu() {
    if (!AfxGetAppSettings().bAlwaysUseShortMenu && (IsMenuHidden() || IsD3DFullScreenMode())) {
        return m_mainPopupMenu.GetSubMenu(0);
    } else {
        return m_popupMenu.GetSubMenu(0);
    }
}

void CMainFrame::OnMenuPlayerShort()
{
    OnMenu(GetShortMenu());
}

void CMainFrame::OnMenuPlayerLong()
{
    OnMenu(m_mainPopupMenu.GetSubMenu(0));
}

void CMainFrame::OnMenuFilters()
{
    SetupFiltersSubMenu();
    OnMenu(&m_filtersMenu);
}

void CMainFrame::OnUpdatePlayerStatus(CCmdUI* pCmdUI)
{
    const MLS loadState = GetLoadState();
    // Only a message flagged to survive media loads (the API status message) may be
    // shown outside the LOADED state; an ordinary transient message must not mask
    // "Opening..." or a closing error while a load is in progress or has failed.
    if (!m_tempstatus_msg.IsEmpty()
            && (loadState == MLS::LOADED
                || (m_bKeepTempStatusBarVisibleOnMediaLoad && loadState != MLS::CLOSING))) {
        m_wndStatusBar.SetStatusMessage(m_tempstatus_msg);
        if (loadState == MLS::LOADING && AfxGetAppSettings().bUseEnhancedTaskBar && m_pTaskbarList) {
            m_pTaskbarList->SetProgressState(m_hWnd, TBPF_NOPROGRESS);
        }
        return;
    }

    if (loadState == MLS::LOADING) {
        m_wndStatusBar.SetStatusMessage(StrRes(IDS_CONTROLS_OPENING));
        if (AfxGetAppSettings().bUseEnhancedTaskBar && m_pTaskbarList) {
            m_pTaskbarList->SetProgressState(m_hWnd, TBPF_NOPROGRESS);
        }
    } else if (loadState == MLS::LOADED) {
        CString msg;
        if (m_fCapturing) {
            msg.LoadString(IDS_CONTROLS_CAPTURING);

            if (m_pAMDF) {
                long lDropped = 0;
                m_pAMDF->GetNumDropped(&lDropped);
                long lNotDropped = 0;
                m_pAMDF->GetNumNotDropped(&lNotDropped);

                if ((lDropped + lNotDropped) > 0) {
                    msg.AppendFormat(IDS_MAINFRM_37, lDropped + lNotDropped, lDropped);
                }
            }

            CComPtr<IPin> pPin;
            if (m_pCGB && SUCCEEDED(m_pCGB->FindPin(m_wndCaptureBar.m_capdlg.m_pDst, PINDIR_INPUT, nullptr, nullptr, FALSE, 0, &pPin))) {
                LONGLONG size = 0;
                if (CComQIPtr<IStream> pStream = pPin) {
                    pStream->Commit(STGC_DEFAULT);

                    WIN32_FIND_DATA findFileData;
                    HANDLE h = FindFirstFile(m_wndCaptureBar.m_capdlg.m_file, &findFileData);
                    if (h != INVALID_HANDLE_VALUE) {
                        size = ((LONGLONG)findFileData.nFileSizeHigh << 32) | findFileData.nFileSizeLow;

                        if (size < 1024i64 * 1024) {
                            msg.AppendFormat(IDS_MAINFRM_38, size / 1024);
                        } else { //if (size < 1024i64*1024*1024)
                            msg.AppendFormat(IDS_MAINFRM_39, size / 1024 / 1024);
                        }

                        FindClose(h);
                    }
                }

                ULARGE_INTEGER FreeBytesAvailable, TotalNumberOfBytes, TotalNumberOfFreeBytes;
                if (GetDiskFreeSpaceEx(
                            m_wndCaptureBar.m_capdlg.m_file.Left(m_wndCaptureBar.m_capdlg.m_file.ReverseFind('\\') + 1),
                            &FreeBytesAvailable, &TotalNumberOfBytes, &TotalNumberOfFreeBytes)) {
                    if (FreeBytesAvailable.QuadPart < 1024i64 * 1024) {
                        msg.AppendFormat(IDS_MAINFRM_40, FreeBytesAvailable.QuadPart / 1024);
                    } else { //if (FreeBytesAvailable.QuadPart < 1024i64*1024*1024)
                        msg.AppendFormat(IDS_MAINFRM_41, FreeBytesAvailable.QuadPart / 1024 / 1024);
                    }
                }

                if (m_wndCaptureBar.m_capdlg.m_pMux) {
                    __int64 pos = 0;
                    CComQIPtr<IMediaSeeking> pMuxMS = m_wndCaptureBar.m_capdlg.m_pMux;
                    if (pMuxMS && SUCCEEDED(pMuxMS->GetCurrentPosition(&pos)) && pos > 0) {
                        double bytepersec = 10000000.0 * size / pos;
                        if (bytepersec > 0) {
                            m_rtDurationOverride = REFERENCE_TIME(10000000.0 * (FreeBytesAvailable.QuadPart + size) / bytepersec);
                        }
                    }
                }

                if (m_wndCaptureBar.m_capdlg.m_pVidBuffer
                        || m_wndCaptureBar.m_capdlg.m_pAudBuffer) {
                    int nFreeVidBuffers = 0, nFreeAudBuffers = 0;
                    if (CComQIPtr<IBufferFilter> pVB = m_wndCaptureBar.m_capdlg.m_pVidBuffer) {
                        nFreeVidBuffers = pVB->GetFreeBuffers();
                    }
                    if (CComQIPtr<IBufferFilter> pAB = m_wndCaptureBar.m_capdlg.m_pAudBuffer) {
                        nFreeAudBuffers = pAB->GetFreeBuffers();
                    }

                    msg.AppendFormat(IDS_MAINFRM_42, nFreeVidBuffers, nFreeAudBuffers);
                }
            }
        } else if (m_bBuffering) {
            if (m_pAMNS) {
                long BufferingProgress = 0;
                if (SUCCEEDED(m_pAMNS->get_BufferingProgress(&BufferingProgress)) && BufferingProgress > 0) {
                    msg.Format(IDS_CONTROLS_BUFFERING, BufferingProgress);

                    __int64 start = 0, stop = 0;
                    m_wndSeekBar.GetRange(start, stop);
                    m_fLiveWM = (stop == start);
                }
            }
        } else if (m_pAMOP) {
            LONGLONG t = 0, c = 0;
            if (SUCCEEDED(m_pAMOP->QueryProgress(&t, &c)) && t > 0 && c < t) {
                msg.Format(IDS_CONTROLS_BUFFERING, c * 100 / t);
            } else {
                m_pAMOP.Release();
            }
        }

        if (msg.IsEmpty()) {
            int msg_id = 0;
            switch (m_CachedFilterState) {
                case State_Stopped:
                    msg_id = IDS_CONTROLS_STOPPED;
                    break;
                case State_Paused:
                    msg_id = IDS_CONTROLS_PAUSED;
                    break;
                case State_Running:
                    msg_id = IDS_CONTROLS_PLAYING;
                    break;
            }
            if (m_fFrameSteppingActive) {
                msg_id = IDS_CONTROLS_PAUSED;
            }
            if (msg_id) {
                msg.LoadString(msg_id);

                if (m_bUsingDXVA && (msg_id == IDS_CONTROLS_PAUSED || msg_id == IDS_CONTROLS_PLAYING)) {
                    msg.AppendFormat(_T(" %s"), ResStr(IDS_HW_INDICATOR).GetString());
                }
            }

            auto& s = AfxGetAppSettings();

            CString videoinfo;
            CString fpsinfo;
            CStringW audioinfo;
            if (s.bShowVideoInfoInStatusbar && (!m_statusbarVideoFormat.IsEmpty() || !m_statusbarVideoSize.IsEmpty())) {                  
                if(!m_statusbarVideoFormat.IsEmpty()) {
                    videoinfo.Append(m_statusbarVideoFormat);
                }
                if(!m_statusbarVideoSize.IsEmpty()) {
                    if(!m_statusbarVideoFormat.IsEmpty()) {
                        videoinfo.AppendChar(_T(' '));
                    }
                    videoinfo.Append(m_statusbarVideoSize);
                }
            }
            if (s.bShowFPSInStatusbar && m_pCAP) {
                if (m_dSpeedRate != 1.0) {
                    fpsinfo.Format(_T("%.2lf fps (%.2lfx)"), m_pCAP->GetFPS(), m_dSpeedRate);
                } else {
                    fpsinfo.Format(_T("%.2lf fps"), m_pCAP->GetFPS());
                }
            }

            if (s.bShowAudioFormatInStatusbar && !m_statusbarAudioFormat.IsEmpty()) {
                audioinfo = m_statusbarAudioFormat;
            }

            if (!videoinfo.IsEmpty() || !fpsinfo.IsEmpty()) {
                CStringW tinfo = L"";
                AppendWithDelimiter(tinfo, videoinfo);
                AppendWithDelimiter(tinfo, fpsinfo);
                msg.Append(L"\u2001[" + tinfo + L"]");
            }

            if (!audioinfo.IsEmpty()) {
                msg.Append(L"\u2001[" + audioinfo);
                if (s.bShowLangInStatusbar && !currentAudioLang.IsEmpty()) {
                    msg.Append(L" " + currentAudioLang);
                }
                msg.Append(L"]");
            }

            if (s.bShowLangInStatusbar) {
                bool showaudiolang = audioinfo.IsEmpty() && !currentAudioLang.IsEmpty();
                if (showaudiolang || !currentSubLang.IsEmpty()) {
                    msg.Append(_T("\u2001["));
                    if (showaudiolang) {
                        msg.Append(L"AUD: " + currentAudioLang);
                    }
                    if (!currentSubLang.IsEmpty()) {
                        if (showaudiolang) {
                            msg.Append(_T(", "));
                        }
                        msg.Append(L"SUB: " + currentSubLang);
                    }
                    msg.Append(_T("]"));
                }
            }
            if (s.bShowABMarksInStatusbar) {
                if (abRepeat) {
                    REFERENCE_TIME actualB = abRepeat.positionB;
                    if (actualB == 0) {
                        REFERENCE_TIME start = 0;
                        m_wndSeekBar.GetRange(start, actualB);
                    }
                    bool showhours = (actualB >= 35995000000) || (abRepeat.positionA >= 35995000000);
                    CString timeMarkA = showhours ? ReftimeToString2(abRepeat.positionA) : ReftimeToString3(abRepeat.positionA);
                    CString timeMarkB = showhours ? ReftimeToString2(actualB) : ReftimeToString3(actualB);
                    msg.AppendFormat(_T("\u2001[A-B %s > %s]"), timeMarkA.GetString(), timeMarkB.GetString());
                }
            }
        }

        m_wndStatusBar.SetStatusMessage(msg);
    } else if (loadState == MLS::CLOSING) {
        m_wndStatusBar.SetStatusMessage(StrRes(IDS_CONTROLS_CLOSING));
        if (AfxGetAppSettings().bUseEnhancedTaskBar && m_pTaskbarList) {
            m_pTaskbarList->SetProgressState(m_hWnd, TBPF_NOPROGRESS);
        }
    } else {
        m_wndStatusBar.SetStatusMessage(m_closingmsg);
    }
}

LRESULT CMainFrame::OnFilePostOpenmedia(WPARAM wParam, LPARAM lParam)
{
    auto& s = AfxGetAppSettings();
        
    if (m_pGB && GetLoadState() == MLS::LOADING) {
        if (USE_LOGGER(s)) {
            PLAYER_LOG(_T("CMainFrame::OnFilePostOpenmedia (thread %lu)"), GetCurrentThreadId());
        }
    } else {
        if (USE_LOGGER(s)) {
            PLAYER_LOG(_T("CMainFrame::OnFilePostOpenmedia (thread %lu) - unexpected state"), GetCurrentThreadId());
            FLUSH_LOGGER();
        }
        ASSERT(FALSE);
        return 1;
    }

    // from this on
    m_bOpenMediaActive = false;
    m_OpenMediaFailedCount = 0;
    m_bSettingUpMenus = true;

    SetLoadState(MLS::LOADED);
    ASSERT(GetMediaStateDirect() == State_Stopped);

    // destroy invisible top-level d3dfs window if there is no video renderer
    if (HasDedicatedFSVideoWindow() && !m_pMFVDC && !m_pVMRWC && !m_pVW) {
        m_pDedicatedFSVideoWnd->DestroyWindow();
        if (s.IsD3DFullscreen()) {
            m_fStartInD3DFullscreen = true;
        } else {
            m_fStartInFullscreenSeparate = true;
        }
    }

    // auto-change monitor mode if requested
    if (s.autoChangeFSMode.bEnabled && IsFullScreenMode()) {
        AutoChangeMonitorMode();
        // make sure the fullscreen window is positioned properly after the mode change,
        // OnWindowPosChanging() will take care of that
        if (m_bOpeningInAutochangedMonitorMode && m_fFullScreen) {
            CRect rect;
            GetWindowRect(rect);
            MoveWindow(rect);
        }
    }

    // set shader selection
    if (m_pCAP || m_pCAP2) {
        bool pre = m_bToggleShader && s.m_Shaders.GetCurrentPreset().GetPreResize().size() > 0;
        bool post = m_bToggleShaderScreenSpace && s.m_Shaders.GetCurrentPreset().GetPostResize().size() > 0;
        if (pre || post) {
            SetShaders(pre, post);
        }
    }

    // load keyframes for fast-seek
    if (wParam == PM_FILE) {
        LoadKeyFrames();
    }

    // remember OpenMediaData for later use
    m_lastOMD.Free();
    m_lastOMD.Attach((OpenMediaData*)lParam);
    if (!m_lastOMD->title) {
        ASSERT(false);
        m_lastOMD->title = L"";
    }

    // the media opened successfully, we don't want to jump trough it anymore
    UINT lastSkipDirection = m_nLastSkipDirection;
    m_nLastSkipDirection = 0;

    // let the EDL do its magic
    if (s.fEnableEDLEditor && !m_lastOMD->title.IsEmpty()) {
        m_wndEditListEditor.OpenFile(m_lastOMD->title);
    }

    // initiate Capture panel with the new media
    if (auto pDeviceData = dynamic_cast<OpenDeviceData*>(m_lastOMD.m_p)) {
        m_wndCaptureBar.m_capdlg.SetVideoInput(pDeviceData->vinput);
        m_wndCaptureBar.m_capdlg.SetVideoChannel(pDeviceData->vchannel);
        m_wndCaptureBar.m_capdlg.SetAudioInput(pDeviceData->ainput);
    }

    // current playlist item was loaded successfully
    m_wndPlaylistBar.SetCurValid(true);

    // set item duration in the playlist
    // TODO: GetDuration() should be refactored out of this place, to some aggregating class
    REFERENCE_TIME rtDur = 0;
    if (m_pMS && m_pMS->GetDuration(&rtDur) == S_OK) {
        m_wndPlaylistBar.SetCurTime(rtDur);
    }

    // process /pns command-line arg, then discard it
    ApplyPanNScanPresetString();

    // initiate toolbars with the new media
    OpenSetupInfoBar();
    OpenSetupStatsBar();
    OpenSetupStatusBar();
    OpenSetupCaptureBar();

    // Load cover-art
    if (m_fAudioOnly || HasDedicatedFSVideoWindow()) {
        UpdateControlState(CMainFrame::UPDATE_MEDIA_ART);
    }

    if (s.bOpenRecPanelWhenOpeningDevice) {
        if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
            // show navigation panel when it's available and not disabled
            if (!s.fHideNavigation) {
                m_wndNavigationBar.m_navdlg.UpdateElementList();
                if (!m_controls.ControlChecked(CMainFrameControls::Panel::NAVIGATION)) {
                    m_controls.ToggleControl(CMainFrameControls::Panel::NAVIGATION);
                }
                else {
                    ASSERT(FALSE);
                }
            }
        }
        else if (GetPlaybackMode() == PM_ANALOG_CAPTURE) {
            // show capture bar
            if (!s.bHideCaptureSettings) {
                if (!m_controls.ControlChecked(CMainFrameControls::Panel::CAPTURE)) {
                    m_controls.ToggleControl(CMainFrameControls::Panel::CAPTURE);
                } else {
                    ASSERT(FALSE);
                }
            }
        }
    }

    // we don't want to wait until timers initialize the seekbar and the time counter
    OnTimer(TIMER_STREAMPOSPOLLER);
    OnTimer(TIMER_STREAMPOSPOLLER2);

    if (m_AngleX != 0 || m_AngleY != 0 || m_AngleZ != 0) {
        PerformFlipRotate();
    }

    bool go_fullscreen = s.fLaunchfullscreen && !m_fAudioOnly && !IsFullScreenMode() && lastSkipDirection == 0 && !(s.nCLSwitches & CLSW_THUMBNAILS);

    // auto-zoom if requested
    if (IsWindowVisible() && s.fRememberZoomLevel && !IsFullScreenMode() && !IsZoomed() && !IsIconic() && !IsAeroSnapped()) {
        if (go_fullscreen) {
            m_bNeedZoomAfterFullscreenExit = true;
        }
        ZoomVideoWindow(ZOOM_DEFAULT_LEVEL, go_fullscreen);
    }

    if (go_fullscreen) {
        OnViewFullscreen();
    }

    // Add temporary flag to allow EC_VIDEO_SIZE_CHANGED event to stabilize window size
    // for 5 seconds since playback starts
    m_bAllowWindowZoom = true;
    m_timerOneTime.Subscribe(TimerOneTimeSubscriber::AUTOFIT_TIMEOUT, [this]
    { m_bAllowWindowZoom = false; }, 5000);

    // update control bar areas and paint bypassing the message queue
    RecalcLayout();
    UpdateWindow();

    // the window is repositioned and repainted, video renderer rect is ready to be set -
    // OnPlayPlay()/OnPlayPause() will take care of that
    m_bDelaySetOutputRect = false;

    if (s.nCLSwitches & CLSW_THUMBNAILS) {
        MoveVideoWindow(false, true);
        MediaControlPause(true);
        SendMessageW(WM_COMMAND, ID_CMDLINE_SAVE_THUMBNAILS);
        m_bSettingUpMenus = false;
        m_bRememberFilePos = false;
        SendMessageW(WM_COMMAND, ID_FILE_EXIT);
        return 0;
    }

    MediaTransportControlSetMedia();

    // start playback if requested
    m_bFirstPlay = true;
    const auto uModeChangeDelay = s.autoChangeFSMode.uDelay * 1000;
    if (!(s.nCLSwitches & CLSW_OPEN) && (s.nLoops > 0)) {
        if (m_bOpeningInAutochangedMonitorMode && uModeChangeDelay) {
            m_timerOneTime.Subscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE,
                std::bind(&CMainFrame::OnPlayPlay, this), uModeChangeDelay);
        } else {
            OnPlayPlay();
        }
    } else {
        // OnUpdatePlayPauseStop() will decide if we can pause the media
        if (m_bOpeningInAutochangedMonitorMode && uModeChangeDelay) {
            m_timerOneTime.Subscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE,
                [this] { OnCommand(ID_PLAY_PAUSE, 0); }, uModeChangeDelay);
        } else {
            OnCommand(ID_PLAY_PAUSE, 0);
        }
    }
    s.nCLSwitches &= ~CLSW_OPEN;  

    LoadDynamicMenus();

    // notify listeners
    if (GetPlaybackMode() != PM_DIGITAL_CAPTURE) {
        SendNowPlayingToApi();
    }

    if (CanPreviewUse() && m_wndSeekBar.IsVisible()) {
        CPoint point;
        GetCursorPos(&point);

        CRect rect;
        m_wndSeekBar.GetWindowRect(&rect);
        if (rect.PtInRect(point)) {
            m_wndSeekBar.PreviewWindowShow(point);
        }
    }

    m_bSettingUpMenus = false;

    // The device is open now, which is the one precondition DoTunerScan has.
    // Consume the switch so a later open cannot start a second scan.
    if ((s.nCLSwitches & CLSW_DVBSCAN) && GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
        s.nCLSwitches &= ~CLSW_DVBSCAN;
        m_bHeadlessDVBScan = true;
        StartHeadlessDVBScan();
    }

    return 0;
}

LRESULT CMainFrame::OnOpenMediaFailed(WPARAM wParam, LPARAM lParam)
{
    ASSERT(GetLoadState() == MLS::LOADING);
    SetLoadState(MLS::FAILING);

    ASSERT(GetCurrentThreadId() == AfxGetApp()->m_nThreadID);
    const auto& s = AfxGetAppSettings();

    if (USE_LOGGER(s)) {
        PLAYER_LOG(_T("CMainFrame::OnOpenMediaFailed (thread %lu)"), GetCurrentThreadId());
        FLUSH_LOGGER();
    }

    // The other way a headless scan can be left with nothing to wait for: the
    // device was configured but would not open. Quit rather than sit idle.
    if (AfxGetAppSettings().nCLSwitches & CLSW_DVBSCAN) {
        TRACE(_T("/dvbscan: the capture device failed to open, abandoning the scan\n"));
        AfxGetAppSettings().nCLSwitches &= ~CLSW_DVBSCAN;
        PostMessage(WM_CLOSE);
    }

    m_lastOMD.Free();
    m_lastOMD.Attach((OpenMediaData*)lParam);
    if (!m_lastOMD->title) {
        ASSERT(false);
        m_lastOMD->title = L"";
    }

    bool bOpenNextInPlaylist = false;
    bool bAfterPlaybackEvent = false;

    m_bOpenMediaActive = false;
    m_OpenMediaFailedCount++;

    m_reloadFilename.Empty();
    m_rtReloadPos = -1;
    reloadABRepeat = ABRepeat();
    m_iReloadAudioIdx = -1;
    m_iReloadSubIdx = -1;

    if (wParam == PM_FILE && m_OpenMediaFailedCount < 5) {
        CPlaylistItem pli;
        if (m_wndPlaylistBar.GetCur(pli) && pli.m_bYoutubeDL && m_sydlLastProcessURL != pli.m_ydlSourceURL) {
            OpenCurPlaylistItem(0, true);  // Try to reprocess if failed first time.
            return 0;
        }
        if (m_wndPlaylistBar.GetCount() == 1) {
            if (m_nLastSkipDirection == ID_NAVIGATE_SKIPBACK) {
                bOpenNextInPlaylist = SearchInDir(false, s.bLoopFolderOnPlayNextFile);
                if (!bOpenNextInPlaylist) {
                    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_FIRST_IN_FOLDER));
                }
            } else if (m_nLastSkipDirection == ID_NAVIGATE_SKIPFORWARD) {
                bOpenNextInPlaylist = SearchInDir(true, s.bLoopFolderOnPlayNextFile);
                if (!bOpenNextInPlaylist) {
                    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_LAST_IN_FOLDER));
                }
            }
        } else {
            m_wndPlaylistBar.SetCurValid(false);

            if (m_wndPlaylistBar.IsAtEnd()) {
                m_nLoops++;
            }

            if (s.fLoopForever || m_nLoops < s.nLoops) {
                if (m_nLastSkipDirection == ID_NAVIGATE_SKIPBACK) {
                    bOpenNextInPlaylist = m_wndPlaylistBar.SetPrev();
                } else {
                    bOpenNextInPlaylist = m_wndPlaylistBar.SetNext();
                }
            } else {
                bAfterPlaybackEvent = true;
            }
        }
    }

    CloseMedia(bOpenNextInPlaylist);

    if (m_OpenMediaFailedCount >= 5) {
        m_wndPlaylistBar.SetCurValid(false);
        if (m_wndPlaylistBar.IsAtEnd()) {
            m_nLoops++;
        }
        if (s.fLoopForever || m_nLoops < s.nLoops) {
            if (m_nLastSkipDirection == ID_NAVIGATE_SKIPBACK) {
                m_wndPlaylistBar.SetPrev();
            } else {
                m_wndPlaylistBar.SetNext();
            }
        }
        m_OpenMediaFailedCount = 0;
    }
    else if (bOpenNextInPlaylist) {
        OpenCurPlaylistItem();
    }
    else if (bAfterPlaybackEvent) {
        DoAfterPlaybackEvent();
    }

    if (!bOpenNextInPlaylist) {
        // Open failed and we are not chaining to another file: reveal the status bar (if a
        // preset hides it) so the error message is visible, until the next media load.
        ShowStatusBarForMessage();
    }

    return 0;
}

void CMainFrame::OnFilePostClosemedia(bool bNextIsQueued/* = false*/)
{
    SetPlaybackMode(PM_NONE);
    SetLoadState(MLS::CLOSED);

    abRepeat = ABRepeat();
    m_kfs.clear();

    m_nCurSubtitle = -1;
    m_lSubtitleShift = 0;

    CAppSettings& s = AfxGetAppSettings();
    if (!s.fSavePnSZoom) {
        m_AngleX = m_AngleY = m_AngleZ = 0;
        m_ZoomX = m_ZoomY = 1.0;
        m_PosX = m_PosY = 0.5;
    }

    if (m_closingmsg.IsEmpty()) {
        m_closingmsg.LoadString(IDS_CONTROLS_CLOSED);
    }

    m_wndView.SetVideoRect();
    m_wndSeekBar.Enable(false);
    m_wndSeekBar.SetRange(0, 0);
    m_wndSeekBar.SetPos(0);
    m_wndSeekBar.RemoveChapters();
    m_wndInfoBar.RemoveAllLines();
    m_wndStatsBar.RemoveAllLines();
    m_wndStatusBar.Clear();
    m_wndStatusBar.ShowTimer(false);
    m_wndSeekBar.UpdateTime(); // clear the seekbar time section (durationless media skips SetRange's repaint)
    currentAudioLang.Empty();
    currentSubLang.Empty();
    m_OSD.SetRange(0);
    m_OSD.SetPos(0);
    m_Lcd.SetMediaRange(0, 0);
    m_Lcd.SetMediaPos(0);
    m_statusbarVideoFormat.Empty();
    m_statusbarVideoSize.Empty();

    m_VidDispName.Empty();
    m_AudDispName.Empty();
    m_HWAccelType = L"";

    if (!bNextIsQueued) {
        UpdateControlState(CMainFrame::UPDATE_MEDIA_ART);
        RecalcLayout();
    }

    if (s.fEnableEDLEditor) {
        m_wndEditListEditor.CloseFile();
    }

    if (m_controls.ControlChecked(CMainFrameControls::Panel::SUBRESYNC)) {
        m_controls.ToggleControl(CMainFrameControls::Panel::SUBRESYNC);
    }

    if (m_controls.ControlChecked(CMainFrameControls::Panel::CAPTURE)) {
        m_controls.ToggleControl(CMainFrameControls::Panel::CAPTURE);
    }
    m_wndCaptureBar.m_capdlg.SetupVideoControls(_T(""), nullptr, nullptr, nullptr);
    m_wndCaptureBar.m_capdlg.SetupAudioControls(_T(""), nullptr, CInterfaceArray<IAMAudioInputMixer>());

    if (m_controls.ControlChecked(CMainFrameControls::Panel::NAVIGATION)) {
        m_controls.ToggleControl(CMainFrameControls::Panel::NAVIGATION);
    }

    //if (!bNextIsQueued) {
        OpenSetupWindowTitle(true);
    //}

    SetAlwaysOnTop(s.iOnTop);

    // try to release external objects
    UnloadUnusedExternalObjects();
    SetTimer(TIMER_UNLOAD_UNUSED_EXTERNAL_OBJECTS, 60000, nullptr);

    if (HasDedicatedFSVideoWindow()) {
        if (IsD3DFullScreenMode()) {
            m_fStartInD3DFullscreen = true;
        } else {
            m_fStartInFullscreenSeparate = true;
        }
        if (!bNextIsQueued) {
            m_pDedicatedFSVideoWnd->DestroyWindow();
        }
    }

    UpdateWindow(); // redraw
}

void CMainFrame::OnBossKey()
{
    // Disable animation
    ANIMATIONINFO AnimationInfo;
    AnimationInfo.cbSize = sizeof(ANIMATIONINFO);
    ::SystemParametersInfo(SPI_GETANIMATION, sizeof(ANIMATIONINFO), &AnimationInfo, 0);
    int m_WindowAnimationType = AnimationInfo.iMinAnimate;
    AnimationInfo.iMinAnimate = 0;
    ::SystemParametersInfo(SPI_SETANIMATION, sizeof(ANIMATIONINFO), &AnimationInfo, 0);

    SendMessage(WM_COMMAND, ID_PLAY_PAUSE);
    if (IsFullScreenMode()) {
        SendMessage(WM_COMMAND, ID_VIEW_FULLSCREEN);
    }
    SendMessage(WM_SYSCOMMAND, SC_MINIMIZE, -1);

    // Enable animation
    AnimationInfo.iMinAnimate = m_WindowAnimationType;
    ::SystemParametersInfo(SPI_SETANIMATION, sizeof(ANIMATIONINFO), &AnimationInfo, 0);
}

void CMainFrame::ToolbarContextMenu(int iItem, int nIndex, CRect buttonRect) {
    CMPCThemeMenu* subMenu = nullptr;

    if (iItem == ID_AUDIOS) {
        SetupAudioSubMenu();
        subMenu = &m_audiosMenu;
    } else if (iItem == ID_SUBTITLES) {
        SetupSubtitlesSubMenu();
        subMenu = &m_subtitlesMenu;
    } else if (iItem == ID_MENU_FILTERS) {
        SetupFiltersSubMenu();
        subMenu = &m_filtersMenu;
    } else if (iItem == ID_MENU_PLAYER_LONG) {
        subMenu = m_mainPopupMenu.GetSubMenu(0);
    } else if (iItem == ID_MENU_PLAYER_SHORT) {
        subMenu = GetShortMenu();
    }
    

    if (subMenu) {
        if (AppNeedsThemedControls()) {
            subMenu->fulfillThemeReqs();
        }
        m_bTBDropdownActive = true;
        TPMPARAMS overlap = { sizeof(TPMPARAMS) };
        overlap.rcExclude = buttonRect;
        subMenu->TrackPopupMenuEx(TPM_LEFTALIGN | TPM_LEFTBUTTON | TPM_VERTICAL | TPM_BOTTOMALIGN, buttonRect.left, buttonRect.top, this, &overlap);

        m_bTBDropdownActive = false;
    }
}

void CMainFrame::OnUpdateAudiosButton(CCmdUI* pCmdUI) {
    pCmdUI->Enable(IsStateLoaded() && m_audiosMenu.GetMenuItemCount() > 0);
}

void CMainFrame::OnUpdateSubtitlesButton(CCmdUI* pCmdUI) {
    pCmdUI->Enable(IsStateLoaded() && m_subtitlesMenu.GetMenuItemCount() > 0);
}

void CMainFrame::OnStreamAudio(UINT nID)
{
    nID -= ID_STREAM_AUDIO_NEXT;

    if (!IsStateLoaded()) {
        return;
    }

    DWORD cStreams = 0;
    if (m_pAudioSwitcherSS && SUCCEEDED(m_pAudioSwitcherSS->Count(&cStreams)) && cStreams > 1) {
        for (DWORD i = 0; i < cStreams; i++) {
            DWORD dwFlags = 0;
            DWORD dwGroup = 0;
            if (FAILED(m_pAudioSwitcherSS->Info(i, nullptr, &dwFlags, nullptr, &dwGroup, nullptr, nullptr, nullptr))) {
                return;
            }
            if (dwFlags & (AMSTREAMSELECTINFO_ENABLED | AMSTREAMSELECTINFO_EXCLUSIVE)) {
                long stream_index = (i + (nID == 0 ? 1 : cStreams - 1)) % cStreams;
                if (SUCCEEDED(m_pAudioSwitcherSS->Enable(stream_index, AMSTREAMSELECTENABLE_ENABLE))) {
                    LCID lcid = 0;
                    CComHeapPtr<WCHAR> pszName;
                    AM_MEDIA_TYPE* pmt = nullptr;
                    if (SUCCEEDED(m_pAudioSwitcherSS->Info(stream_index, &pmt, &dwFlags, &lcid, &dwGroup, &pszName, nullptr, nullptr))) {
                        m_OSD.DisplayMessage(OSD_TOPLEFT, GetStreamOSDString(CString(pszName), lcid, 1));
                        UpdateSelectedAudioStreamInfo(stream_index, pmt, lcid);
                        DeleteMediaType(pmt);
                    }
                }
                break;
            }
        }
    } else if (GetPlaybackMode() == PM_FILE) {
        OnStreamSelect(nID == 0, 1);
    } else if (GetPlaybackMode() == PM_DVD) {
        SendMessage(WM_COMMAND, ID_DVD_AUDIO_NEXT + nID);
    }

    if (m_pBA && !m_fFrameSteppingActive) {
        m_pBA->put_Volume(m_wndToolBar.Volume);
    }
}

void CMainFrame::OnStreamSub(UINT nID)
{
    nID -= ID_STREAM_SUB_NEXT;
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (!m_pSubStreams.IsEmpty()) {
        AfxGetAppSettings().fEnableSubtitles = true;
        SetSubtitle(nID == 0 ? 1 : -1, true, true);
        SetFocus();
    } else if (GetPlaybackMode() == PM_FILE) {
        OnStreamSelect(nID == 0, 2);
    } else if (GetPlaybackMode() == PM_DVD) {
        SendMessage(WM_COMMAND, ID_DVD_SUB_NEXT + nID);
    }
}

void CMainFrame::OnStreamSubOnOff()
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (m_pCAP && !m_pSubStreams.IsEmpty() || m_pDVS) {
        ToggleSubtitleOnOff(true);
        SetFocus();
    } else if (GetPlaybackMode() == PM_DVD) {
        SendMessage(WM_COMMAND, ID_DVD_SUB_ONOFF);
    }
}

void CMainFrame::OnSubtitlesAutoCopy()
{
    CAppSettings& s = AfxGetAppSettings();
    s.bAutoCopySubtitleToClipboard = !s.bAutoCopySubtitleToClipboard;
    ResetAutoCopySubtitle();
    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(s.bAutoCopySubtitleToClipboard ? IDS_OSD_AUTOCOPY_SUBTITLE_ON : IDS_OSD_AUTOCOPY_SUBTITLE_OFF));
}

void CMainFrame::OnDvdAngle(UINT nID)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (m_pDVDI && m_pDVDC) {
        ULONG ulAnglesAvailable, ulCurrentAngle;
        if (SUCCEEDED(m_pDVDI->GetCurrentAngle(&ulAnglesAvailable, &ulCurrentAngle)) && ulAnglesAvailable > 1) {
            ulCurrentAngle += (nID == ID_DVD_ANGLE_NEXT) ? 1 : -1;
            if (ulCurrentAngle > ulAnglesAvailable) {
                ulCurrentAngle = 1;
            } else if (ulCurrentAngle < 1) {
                ulCurrentAngle = ulAnglesAvailable;
            }
            m_pDVDC->SelectAngle(ulCurrentAngle, DVD_CMD_FLAG_Block, nullptr);

            CString osdMessage;
            osdMessage.Format(IDS_AG_ANGLE, ulCurrentAngle);
            m_OSD.DisplayMessage(OSD_TOPLEFT, osdMessage);
        }
    }
}

void CMainFrame::OnDvdAudio(UINT nID)
{
    nID -= ID_DVD_AUDIO_NEXT;

    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (m_pDVDI && m_pDVDC) {
        ULONG nStreamsAvailable, nCurrentStream;
        if (SUCCEEDED(m_pDVDI->GetCurrentAudio(&nStreamsAvailable, &nCurrentStream)) && nStreamsAvailable > 1) {
            DVD_AudioAttributes AATR;
            UINT nNextStream = (nCurrentStream + (nID == 0 ? 1 : nStreamsAvailable - 1)) % nStreamsAvailable;

            HRESULT hr = m_pDVDC->SelectAudioStream(nNextStream, DVD_CMD_FLAG_Block, nullptr);
            if (SUCCEEDED(m_pDVDI->GetAudioAttributes(nNextStream, &AATR))) {
                CString lang;
                CString strMessage;
                if (AATR.Language) {
                    GetLocaleString(AATR.Language, LOCALE_SENGLANGUAGE, lang);
                    currentAudioLang = lang;
                } else {
                    lang.Format(IDS_AG_UNKNOWN, nNextStream + 1);
                    currentAudioLang.Empty();
                }

                CString format = GetDVDAudioFormatName(AATR);
                CString str;

                if (!format.IsEmpty()) {
                    str.Format(IDS_MAINFRM_11,
                               lang.GetString(),
                               format.GetString(),
                               AATR.dwFrequency,
                               AATR.bQuantization,
                               AATR.bNumberOfChannels,
                               ResStr(AATR.bNumberOfChannels > 1 ? IDS_MAINFRM_13 : IDS_MAINFRM_12).GetString());
                    if (FAILED(hr)) {
                        str += _T(" [") + ResStr(IDS_AG_ERROR) + _T("] ");
                    }
                    strMessage.Format(IDS_AUDIO_STREAM, str.GetString());
                    m_OSD.DisplayMessage(OSD_TOPLEFT, strMessage);
                }
            }
        }
    }
}

void CMainFrame::OnDvdSub(UINT nID)
{
    nID -= ID_DVD_SUB_NEXT;

    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (m_pDVDI && m_pDVDC) {
        ULONG ulStreamsAvailable, ulCurrentStream;
        BOOL bIsDisabled;
        if (SUCCEEDED(m_pDVDI->GetCurrentSubpicture(&ulStreamsAvailable, &ulCurrentStream, &bIsDisabled))
                && ulStreamsAvailable > 1) {
            //UINT nNextStream = (ulCurrentStream+(nID==0?1:ulStreamsAvailable-1))%ulStreamsAvailable;
            int nNextStream;

            if (!bIsDisabled) {
                nNextStream = ulCurrentStream + (nID == 0 ? 1 : -1);
            } else {
                nNextStream = (nID == 0 ? 0 : ulStreamsAvailable - 1);
            }

            if (!bIsDisabled && ((nNextStream < 0) || ((ULONG)nNextStream >= ulStreamsAvailable))) {
                m_pDVDC->SetSubpictureState(FALSE, DVD_CMD_FLAG_Block, nullptr);
                m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_SUBTITLE_STREAM_OFF));
            } else {
                HRESULT hr = m_pDVDC->SelectSubpictureStream(nNextStream, DVD_CMD_FLAG_Block, nullptr);

                DVD_SubpictureAttributes SATR;
                m_pDVDC->SetSubpictureState(TRUE, DVD_CMD_FLAG_Block, nullptr);
                if (SUCCEEDED(m_pDVDI->GetSubpictureAttributes(nNextStream, &SATR))) {
                    CString lang;
                    CString strMessage;
                    GetLocaleString(SATR.Language, LOCALE_SENGLANGUAGE, lang);

                    if (FAILED(hr)) {
                        lang += _T(" [") + ResStr(IDS_AG_ERROR) + _T("] ");
                    }
                    strMessage.Format(IDS_SUBTITLE_STREAM, lang.GetString());
                    m_OSD.DisplayMessage(OSD_TOPLEFT, strMessage);
                }
            }
        }
    }
}

void CMainFrame::OnDvdSubOnOff()
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (m_pDVDI && m_pDVDC) {
        ULONG ulStreamsAvailable, ulCurrentStream;
        BOOL bIsDisabled;
        if (SUCCEEDED(m_pDVDI->GetCurrentSubpicture(&ulStreamsAvailable, &ulCurrentStream, &bIsDisabled))) {
            m_pDVDC->SetSubpictureState(bIsDisabled, DVD_CMD_FLAG_Block, nullptr);
        }
    }
}

//
// menu item handlers
//

// file

INT_PTR CMainFrame::DoFileDialogWithLastFolder(CFileDialog& fd, CStringW& lastPath) {
    if (!lastPath.IsEmpty()) {
        fd.m_ofn.lpstrInitialDir = lastPath;
    }
    INT_PTR ret = fd.DoModal();
    if (ret == IDOK) {
        lastPath = GetFolderOnly(fd.m_ofn.lpstrFile);
    }
    return ret;
}


void CMainFrame::OnFileOpenQuick()
{
    if (!IsStateClosedOrLoaded() || !IsWindow(m_wndPlaylistBar)) {
        return;
    }

    CAppSettings& s = AfxGetAppSettings();
    CString filter;
    CAtlArray<CString> mask;
    s.m_Formats.GetFilter(filter, mask);

    DWORD dwFlags = OFN_EXPLORER | OFN_ENABLESIZING | OFN_ALLOWMULTISELECT | OFN_ENABLEINCLUDENOTIFY | OFN_NOCHANGEDIR | OFN_PATHMUSTEXIST | OFN_FILEMUSTEXIST;
    if (!s.fKeepHistory) {
        dwFlags |= OFN_DONTADDTORECENT;
    }

    COpenFileDlg fd(mask, true, nullptr, nullptr, dwFlags, filter, GetModalParent());
    if (DoFileDialogWithLastFolder(fd, s.lastQuickOpenPath) != IDOK) {
        return;
    }

    CAtlList<CString> fns;
    FileDialogUtils::GetSelectedPaths(fd, fns);

    bool fMultipleFiles = false;

    if (fns.GetCount() > 1
            || fns.GetCount() == 1
            && (fns.GetHead()[fns.GetHead().GetLength() - 1] == '\\'
                || fns.GetHead()[fns.GetHead().GetLength() - 1] == '*')) {
        fMultipleFiles = true;
    }

    if (!CloseMediaBeforeOpen()) {
        return;
    }

    if (IsIconic()) {
        ShowWindow(SW_RESTORE);
    }
    SetForegroundWindow();

    if (fns.GetCount() == 1) {
        if (OpenBD(fns.GetHead())) {
            return;
        }
    }

    m_wndPlaylistBar.Open(fns, fMultipleFiles);

    OpenCurPlaylistItem();
}

void CMainFrame::OnFileOpenmedia()
{
    if (!IsStateClosedOrLoaded() || !IsWindow(m_wndPlaylistBar) || IsD3DFullScreenMode()) {
        return;
    }

    static COpenDlg dlg;
    if (IsWindow(dlg.GetSafeHwnd()) && dlg.IsWindowVisible()) {
        dlg.SetForegroundWindow();
        return;
    }
    if (dlg.DoModal() != IDOK || dlg.GetFileNames().IsEmpty()) {
        return;
    }

    if (!dlg.GetAppendToPlaylist()) {
        if (!CloseMediaBeforeOpen()) {
            return;
        }
    }

    if (IsIconic()) {
        ShowWindow(SW_RESTORE);
    }
    SetForegroundWindow();

    CAtlList<CString> filenames;

    if (CanSendToYoutubeDL(dlg.GetFileNames().GetHead())) {
        if (ProcessYoutubeDLURL(dlg.GetFileNames().GetHead(), dlg.GetAppendToPlaylist())) {
            if (!dlg.GetAppendToPlaylist()) {
                OpenCurPlaylistItem();
            }
            return;
        } else if (IsOnYDLWhitelist(dlg.GetFileNames().GetHead())) {
            m_closingmsg = L"Failed to extract stream URL with yt-dlp/youtube-dl";
            m_wndStatusBar.SetStatusMessage(m_closingmsg);
            // don't bother trying to open this website URL directly
            return;
        }
    }

    filenames.AddHeadList(&dlg.GetFileNames());

    if (!dlg.HasMultipleFiles()) {
        if (OpenBD(filenames.GetHead())) {
            return;
        }
    }

    if (dlg.GetAppendToPlaylist()) {
        m_wndPlaylistBar.Append(filenames, dlg.HasMultipleFiles());
    } else {
        SendStatusMessage(_T("Loading..."), 500);

        m_wndPlaylistBar.Open(filenames, dlg.HasMultipleFiles());

        OpenCurPlaylistItem();
    }
}

LRESULT CMainFrame::OnMPCVRSwitchFullscreen(WPARAM wParam, LPARAM lParam)
{
    const auto& s = AfxGetAppSettings();
    m_bIsMPCVRExclusiveMode = static_cast<bool>(wParam);

    m_OSD.Stop();
    if (m_bIsMPCVRExclusiveMode) {
        TRACE(L"MPCVR exclusive full screen\n");
        bool excl_mode_controls = IsFullScreenMainFrame();
        if (excl_mode_controls && m_wndPlaylistBar.IsVisible()) {
            m_wndPlaylistBar.SetHiddenDueToFullscreen(true);
        }
        if (s.fShowOSD || s.fShowDebugInfo) {
            if (m_pVMB || m_pMFVMB) {
                m_OSD.Start(m_pVideoWnd, m_pVMB, m_pMFVMB, excl_mode_controls);
            }
        }
    } else {
        if (s.fShowOSD || s.fShowDebugInfo) {
            m_OSD.Start(m_pOSDWnd);
            OSDBarSetPos();
        }
        if (m_wndPlaylistBar.IsHiddenDueToFullscreen()) {
            m_wndPlaylistBar.SetHiddenDueToFullscreen(false);
        }
    }

    return 0;
}

void CMainFrame::OnUpdateFileOpen(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(IsStateClosedOrLoaded());
}

BOOL CMainFrame::OnCopyData(CWnd* pWnd, COPYDATASTRUCT* pCDS)
{
    if (AfxGetMyApp()->m_fClosingState) {
        return FALSE;
    }

    CAppSettings& s = AfxGetAppSettings();

    if (USE_LOGGER(s)) {
        PLAYER_LOG(_T("CMainFrame::OnCopyData"));
    }

    if (pCDS->dwData != 0x6ABE51 || pCDS->cbData < sizeof(DWORD)) {
        if (s.hMasterWnd) {
            ProcessAPICommand(pWnd ? pWnd->GetSafeHwnd() : nullptr, pCDS);
            return TRUE;
        } else {
            return FALSE;
        }
    }

    if (m_bScanDlgOpened) {
        return FALSE;
    }

    DWORD len = *((DWORD*)pCDS->lpData);
    TCHAR* pBuff = (TCHAR*)((DWORD*)pCDS->lpData + 1);
    TCHAR* pBuffEnd = (TCHAR*)((BYTE*)pBuff + pCDS->cbData - sizeof(DWORD));

    CAtlList<CString> cmdln;

    while (len-- > 0 && pBuff < pBuffEnd) {
        CString str(pBuff);
        pBuff += str.GetLength() + 1;

        cmdln.AddTail(str);
    }

    s.ParseCommandLine(cmdln);

    if (s.nCLSwitches & CLSW_SLAVE) {
        m_lastApiVolume = GetVolume();
        m_lastApiMute = IsMuted() ? 1 : 0;
        m_hostIntApiVersion = 0; // new host: integer channel unconfirmed until it says HELLO
        SendAPICommand(CMD_CONNECT, L"%d", PtrToInt(GetSafeHwnd()));
        s.nCLSwitches &= ~CLSW_SLAVE;
    }

    POSITION pos = s.slFilters.GetHeadPosition();
    while (pos) {
        CString fullpath = MakeFullPath(s.slFilters.GetNext(pos));

        CPath tmp(fullpath);
        tmp.RemoveFileSpec();
        tmp.AddBackslash();
        CString path = tmp;

        WIN32_FIND_DATA fd;
        ZeroMemory(&fd, sizeof(WIN32_FIND_DATA));
        HANDLE hFind = FindFirstFile(fullpath, &fd);
        if (hFind != INVALID_HANDLE_VALUE) {
            do {
                if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) {
                    continue;
                }

                CFilterMapper2 fm2(false);
                fm2.Register(path + fd.cFileName);
                while (!fm2.m_filters.IsEmpty()) {
                    if (FilterOverride* f = fm2.m_filters.RemoveTail()) {
                        f->fTemporary = true;

                        bool fFound = false;

                        POSITION pos2 = s.m_filters.GetHeadPosition();
                        while (pos2) {
                            FilterOverride* f2 = s.m_filters.GetNext(pos2);
                            if (f2->type == FilterOverride::EXTERNAL && !f2->path.CompareNoCase(f->path)) {
                                fFound = true;
                                break;
                            }
                        }

                        if (!fFound) {
                            CAutoPtr<FilterOverride> p(f);
                            s.m_filters.AddHead(p);
                        }
                    }
                }
            } while (FindNextFile(hFind, &fd));

            FindClose(hFind);
        }
    }

    bool fSetForegroundWindow = false;

    auto applyRandomizeSwitch = [&]() {
        if (s.nCLSwitches & CLSW_RANDOMIZE) {
            m_wndPlaylistBar.Randomize();
            s.nCLSwitches &= ~CLSW_RANDOMIZE;
        }
    };

    if ((s.nCLSwitches & CLSW_DVD) && !s.slFiles.IsEmpty()) {
        if (!CloseMediaBeforeOpen()) {
            return TRUE;
        }
        fSetForegroundWindow = true;

        CAutoPtr<OpenDVDData> p(DEBUG_NEW OpenDVDData());
        if (p) {
            p->path = s.slFiles.GetHead();
            p->subs.AddTailList(&s.slSubs);
            m_wndPlaylistBar.OpenDVD(p->path);
        }
        // ToDo: open indirectly
        OpenMedia(p);
        s.nCLSwitches &= ~CLSW_DVD;
    } else if (s.nCLSwitches & CLSW_CD) {
        if (GetMediaState() == State_Running) {
            MediaControlPause(true);
        }
        fSetForegroundWindow = true;

        CAtlList<CString> sl;
        if (!s.slFiles.IsEmpty()) {
            GetOpticalDiskType(s.slFiles.GetHead()[0], sl);
        } else {
            CString dir;
            dir.ReleaseBufferSetLength(GetCurrentDirectory(2048, dir.GetBuffer(2048)));

            GetOpticalDiskType(dir[0], sl);

            for (TCHAR drive = _T('A'); sl.IsEmpty() && drive <= _T('Z'); drive++) {
                GetOpticalDiskType(drive, sl);
            }
        }

        m_wndPlaylistBar.Open(sl, true);
        applyRandomizeSwitch();
        s.nCLSwitches &= ~CLSW_CD;
        PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
    } else if (s.nCLSwitches & (CLSW_DEVICE | CLSW_DVBSCAN)) {
        // OnFileOpendevice shows the capture options page and returns when no
        // device is configured. Interactively that is a prompt; for a headless
        // run it is a modal nobody can answer, and the process would sit there
        // with no device, no scan and nothing to time out. Check the same
        // condition first and fail the run instead.
        if ((s.nCLSwitches & CLSW_DVBSCAN) && s.iDefaultCaptureDevice == 0 &&
                s.strAnalogVideo == L"dummy" && s.strAnalogAudio == L"dummy") {
            TRACE(_T("/dvbscan: no capture device configured, nothing to scan\n"));
            s.nCLSwitches &= ~CLSW_DVBSCAN;
            PostMessage(WM_CLOSE);
        } else {
            // /dvbscan implies opening the capture device, because DoTunerScan
            // only runs in PM_DIGITAL_CAPTURE. CLSW_DVBSCAN is deliberately
            // left set: OnFilePostOpenmedia consumes it once the device is up.
            PostMessage(WM_COMMAND, ID_FILE_OPENDEVICE);
            s.nCLSwitches &= ~CLSW_DEVICE;
        }
    } else if (!s.slFiles.IsEmpty()) {
        CAtlList<CString> sl;
        sl.AddTailList(&s.slFiles);

        PathUtils::ParseDirs(sl);

        bool fMulti = sl.GetCount() > 1;
        if (!fMulti) {
            sl.AddTailList(&s.slDubs);
        }

        if (OpenBD(s.slFiles.GetHead())) {
            // Nothing more to do
        } else if (!fMulti && CPath(s.slFiles.GetHead() + _T("\\VIDEO_TS")).IsDirectory()) {
            fSetForegroundWindow = true;

            if (GetMediaState() == State_Running) {
                MediaControlPause(true);
            }

            CAutoPtr<OpenDVDData> p(DEBUG_NEW OpenDVDData());
            if (p) {
                p->path = s.slFiles.GetHead();
                p->subs.AddTailList(&s.slSubs);
                m_wndPlaylistBar.OpenDVD(p->path);
            }
            // ToDo: open indirectly
            OpenMedia(p);
        } else {
            ULONGLONG tcnow = GetTickCount64();
            // Opening a multi-file selection in Explorer spawns one process per file. Those arrive here in
            // arbitrary order, so the entries added by the second and later ones are sorted back into place.
            bool bSameSelection = m_dwLastRun && ((tcnow - m_dwLastRun) < s.iRedirectOpenToAppendThreshold);
            if (bSameSelection) {
                s.nCLSwitches |= CLSW_ADD;
            }
            m_dwLastRun = tcnow;
            bool bRandomize = !!(s.nCLSwitches & CLSW_RANDOMIZE);

            if ((s.nCLSwitches & CLSW_ADD) && !IsPlaylistEmpty()) {
                if (!bSameSelection) { // a new selection starts at the current end of the playlist
                    m_nLastAppendSelectionIndex = (int)m_wndPlaylistBar.GetCount();
                }

                POSITION pos2 = sl.GetHeadPosition();
                while (pos2) {
                    CString fn = sl.GetNext(pos2);
                    if (!CanSendToYoutubeDL(fn) || !ProcessYoutubeDLURL(fn, true)) {
                        CAtlList<CString> sl2;
                        sl2.AddHead(fn);
                        m_wndPlaylistBar.Append(sl2, false, &s.slSubs);
                    }
                }

                applyRandomizeSwitch();

                if (s.nCLSwitches & (CLSW_OPEN | CLSW_PLAY)) {
                    m_wndPlaylistBar.SetLast();
                    if ((s.nCLSwitches & CLSW_STARTVALID) && s.rtStart > 0 || s.abRepeat) {
                        m_reloadFilename = m_wndPlaylistBar.GetCurFileName();
                        m_rtReloadPos = s.rtStart;
                        reloadABRepeat = s.abRepeat;
                        m_iReloadAudioIdx = -1;
                        m_iReloadSubIdx = -1;
                    }
                    PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
                }

                // Done last so that it does not interfere with the item selected above. Sorting only moves
                // list nodes around, so the playlist position stays on the same item.
                if (bSameSelection && !bRandomize) {
                    m_wndPlaylistBar.SortByPathFrom(m_nLastAppendSelectionIndex);
                }
            } else {
                fSetForegroundWindow = true;
                m_nLastAppendSelectionIndex = 0; // the playlist gets replaced below

                if (GetMediaState() == State_Running) {
                    MediaControlPause(true);
                }

                if (fMulti || sl.GetCount() == 1) {
                    bool first = true;
                    POSITION pos2 = sl.GetHeadPosition();
                    while (pos2) {
                        CString fn = sl.GetNext(pos2);
                        if (!CanSendToYoutubeDL(fn) || !ProcessYoutubeDLURL(fn, !first, false)) {
                            CAtlList<CString> sl2;
                            sl2.AddHead(fn);
                            if (first) {
                                m_wndPlaylistBar.Open(sl2, false, &s.slSubs);
                            } else {
                                m_wndPlaylistBar.Append(sl2, false, &s.slSubs);
                            }
                        }
                        first = false;
                    }
                } else {
                    // video + dub
                    m_wndPlaylistBar.Open(sl, false, &s.slSubs);
                }

                applyRandomizeSwitch();
                if (sl.GetCount() != 1 || !IsPlaylistFile(sl.GetHead())) { //playlists already set first pos (or saved pos)
                    m_wndPlaylistBar.SetFirst();
                }

                if ((s.nCLSwitches & CLSW_STARTVALID) && s.rtStart > 0 || s.abRepeat) {
                    m_reloadFilename = m_wndPlaylistBar.GetCurFileName();
                    m_rtReloadPos = s.rtStart;
                    reloadABRepeat = s.abRepeat;
                    m_iReloadAudioIdx = -1;
                    m_iReloadSubIdx = -1;
                }
                PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);

                s.nCLSwitches &= ~CLSW_STARTVALID;
                s.rtStart = 0;
            }
            s.nCLSwitches &= ~CLSW_ADD;
        }
    } else if ((s.nCLSwitches & CLSW_PLAY) && !IsPlaylistEmpty()) {
        if ((s.nCLSwitches & CLSW_STARTVALID) && s.rtStart > 0 || s.abRepeat) {
            m_reloadFilename = m_wndPlaylistBar.GetCurFileName();
            m_rtReloadPos = s.rtStart;
            reloadABRepeat = s.abRepeat;
            m_iReloadAudioIdx = -1;
            m_iReloadSubIdx = -1;
        }
        PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
    } else {
        applyRandomizeSwitch();
    }

    if (s.nCLSwitches & CLSW_PRESET1) {
        SendMessage(WM_COMMAND, ID_VIEW_PRESETS_MINIMAL);
        s.nCLSwitches &= ~CLSW_PRESET1;
    } else if (s.nCLSwitches & CLSW_PRESET2) {
        SendMessage(WM_COMMAND, ID_VIEW_PRESETS_COMPACT);
        s.nCLSwitches &= ~CLSW_PRESET2;
    } else if (s.nCLSwitches & CLSW_PRESET3) {
        SendMessage(WM_COMMAND, ID_VIEW_PRESETS_NORMAL);
        s.nCLSwitches &= ~CLSW_PRESET3;
    } else if (s.nCLSwitches & CLSW_PRESET4) {
        SendMessage(WM_COMMAND, ID_VIEW_PRESETS_CUSTOM);
        s.nCLSwitches &= ~CLSW_PRESET4;
    }
    if (s.nCLSwitches & CLSW_VOLUME) {
        if (IsMuted()) {
            SendMessage(WM_COMMAND, ID_VOLUME_MUTE);
        }
        m_wndToolBar.SetVolume(s.nCmdVolume);
        s.nCLSwitches &= ~CLSW_VOLUME;
    }
    if (s.nCLSwitches & CLSW_MUTE) {
        if (!IsMuted()) {
            SendMessage(WM_COMMAND, ID_VOLUME_MUTE);
        }
        s.nCLSwitches &= ~CLSW_MUTE;
    }

    if (fSetForegroundWindow && !(s.nCLSwitches & CLSW_NOFOCUS)) {
        SetForegroundWindow();
    }

    return TRUE;
}

int CALLBACK BrowseCallbackProc(HWND hwnd, UINT uMsg, LPARAM lp, LPARAM pData)
{
    switch (uMsg) {
        case BFFM_INITIALIZED: {
            //Initial directory is set here
            const CAppSettings& s = AfxGetAppSettings();
            if (!s.strDVDPath.IsEmpty()) {
                SendMessage(hwnd, BFFM_SETSELECTION, TRUE, (LPARAM)(LPCTSTR)s.strDVDPath);
            }
            break;
        }
        default:
            break;
    }
    return 0;
}

void CMainFrame::OpenDVDOrBD(CStringW path) {
    if (!path.IsEmpty()) {
        AfxGetAppSettings().strDVDPath = path;
        if (!OpenBD(path)) {
            CAutoPtr<OpenDVDData> p(DEBUG_NEW OpenDVDData());
            if (p) {
                p->path = path;
                p->path.Replace(_T('/'), _T('\\'));
                p->path = ForceTrailingSlash(p->path);
                m_wndPlaylistBar.OpenDVD(p->path);
            }
            OpenMedia(p);
        }
    }
}

void CMainFrame::OnFileOpendvd()
{
    if (!IsStateClosedOrLoaded() || IsD3DFullScreenMode()) {
        return;
    }

    CAppSettings& s = AfxGetAppSettings();
    CString strTitle(StrRes(IDS_MAINFRM_46));
    CString path;

    if (s.fUseDVDPath && !s.strDVDPath.IsEmpty()) {
        path = s.strDVDPath;
    } else {
        //strDVDPath is actually used as a default to open without the dialog,
        //but since it is always updated to the last path chosen,
        //we can use it as the default for the dialog, too
        CFolderPickerDialog fd(ForceTrailingSlash(s.strDVDPath), FOS_PATHMUSTEXIST, GetModalParent());
        fd.m_ofn.lpstrTitle = strTitle;

        if (fd.DoModal() == IDOK) {
            path = fd.GetPathName(); //getfolderpath() does not work correctly for CFolderPickerDialog
        } else {
            return;
        }
    }
    OpenDVDOrBD(path);
}

void CMainFrame::OnFileOpendevice()
{
    if (!IsStateClosedOrLoaded()) {
        return;
    }
    if (!m_pAMTuner) { // no need to close if changing channel
        if (!CloseMediaBeforeOpen()) {
            return;
        }
    }

    const CAppSettings& s = AfxGetAppSettings();

    SetForegroundWindow();

    if (IsIconic()) {
        ShowWindow(SW_RESTORE);
    }

    m_wndPlaylistBar.Empty();

    if (s.iDefaultCaptureDevice == 0 && s.strAnalogVideo == L"dummy" && s.strAnalogAudio == L"dummy") {
        // device not configured yet, open settings
        ShowOptions(IDD_PPAGECAPTURE);
        return;
    }

    CAutoPtr<OpenDeviceData> p(DEBUG_NEW OpenDeviceData());
    if (p) {
        p->DisplayName[0] = s.strAnalogVideo;
        p->DisplayName[1] = s.strAnalogAudio;
    }
    OpenMedia(p);
}

void CMainFrame::OnFileOpenOpticalDisk(UINT nID)
{
    if (!IsStateClosedOrLoaded()) {
        return;
    }

    nID -= ID_FILE_OPEN_OPTICAL_DISK_START;

    nID++;
    for (TCHAR drive = _T('A'); drive <= _T('Z'); drive++) {
        CAtlList<CString> sl;

        OpticalDiskType_t discType = GetOpticalDiskType(drive, sl);
        switch (discType) {
            case OpticalDisk_Audio:
            case OpticalDisk_VideoCD:
            case OpticalDisk_DVDVideo:
            case OpticalDisk_BD:
                nID--;
                break;
            default:
                break;
        }

        if (nID == 0) {
            if (OpticalDisk_BD == discType || OpticalDisk_DVDVideo == discType) {
                OpenDVDOrBD(CStringW(drive) + L":\\");
            } else {
                if (!CloseMediaBeforeOpen()) {
                    return;
                }
                SetForegroundWindow();

                if (IsIconic()) {
                    ShowWindow(SW_RESTORE);
                }

                m_wndPlaylistBar.Open(sl, true);
                OpenCurPlaylistItem();
            }
            break;
        }
    }
}

void CMainFrame::OnFileRecycle()
{
    // check if a file is playing
    if (GetLoadState() != MLS::LOADED || GetPlaybackMode() != PM_FILE) {
        return;
    }

    OAFilterState fs = GetMediaState();
    if (fs == State_Running) {
        MediaControlPause(true);
    }

    m_wndPlaylistBar.DeleteFileInPlaylist(m_wndPlaylistBar.m_pl.GetPos());
}

void CMainFrame::OnFileReopen()
{
    if (!m_LastOpenBDPath.IsEmpty() && OpenBD(m_LastOpenBDPath)) {
        return;
    }

    auto& s = AfxGetAppSettings();
    if (USE_LOGGER(s)) {
        PLAYER_LOG(_T("CMainFrame::OnFileReopen"));
    }

    // save playback position
    if (GetLoadState() == MLS::LOADED) {
        if (m_bRememberFilePos && !m_fEndOfStream && m_rtReloadPos == -1 && m_pMS) {
            m_rtReloadPos = m_wndSeekBar.HasDuration() ? m_wndSeekBar.GetPos() : 0;
        }
        reloadABRepeat = abRepeat;
        m_reloadFilename = lastOpenFile;
    }

    PostMessage(WM_MPC_OPENCURPLAYLIST, 1, 0);
}

DROPEFFECT CMainFrame::OnDropAccept(COleDataObject* pDataObject, DWORD dwKeyState, CPoint point)
{
    ClientToScreen(&point);
    if (CMouse::CursorOnRootWindow(point, *this)) {
        UpdateControlState(UPDATE_CONTROLS_VISIBILITY);
        return (dwKeyState & MK_CONTROL) ? (DROPEFFECT_COPY | DROPEFFECT_APPEND)
               : (DROPEFFECT_MOVE | DROPEFFECT_LINK | DROPEFFECT_COPY);
    }

    return DROPEFFECT_NONE;
}

bool CMainFrame::IsImageFile(CStringW fn) {
    if (fn.IsEmpty()) return false;

    CPath path(fn);
    CStringW ext(path.GetExtension());
    return IsImageFileExt(ext);
}

bool CMainFrame::IsImageFileExt(CStringW ext) {
    ext.MakeLower();
    return (
        ext == _T(".jpg") || ext == _T(".jpeg") || ext == _T(".png") || ext == _T(".gif") || ext == _T(".bmp")
        || ext == _T(".tiff") || ext == _T(".jpe") || ext == _T(".tga") || ext == _T(".heic") || ext == _T(".avif")
        || ext == _T(".webp")
    );
}

bool CMainFrame::IsPlaylistFile(CStringW fn) {
    CPath path(fn);
    CStringW ext(path.GetExtension());
    return IsPlaylistFileExt(ext);
}

bool CMainFrame::IsPlaylistFileExt(CStringW ext) {
    return (ext == _T(".m3u") || ext == _T(".m3u8") || ext == _T(".mpcpl") || ext == _T(".pls") || ext == _T(".cue") || ext == _T(".asx"));
}

bool CMainFrame::IsAudioOrVideoFileExt(CStringW ext) {
    return IsPlayableFormatExt(ext);
}

bool CMainFrame::IsAudioFileExt(CStringW ext) {
    const CMediaFormats& mf = AfxGetAppSettings().m_Formats;
    ext.MakeLower();
    return mf.FindExt(ext, true);
}

bool CMainFrame::IsPlayableFormatExt(CStringW ext) {
    const CMediaFormats& mf = AfxGetAppSettings().m_Formats;
    ext.MakeLower();
    return mf.FindExt(ext);
}

bool CMainFrame::CanSkipToExt(CStringW ext, CStringW curExt)
{
    if (IsImageFileExt(curExt)) {
        return IsImageFileExt(ext);
    } else {
        return IsPlayableFormatExt(ext);
    }
}

BOOL IsSubtitleExtension(CString ext)
{
    return (ext == _T(".srt") || ext == _T(".ssa") || ext == _T(".ass") || ext == _T(".idx") || ext == _T(".sub") || ext == _T(".webvtt") || ext == _T(".vtt") || ext == _T(".sup") || ext == _T(".smi") || ext == _T(".psb") || ext == _T(".usf") || ext == _T(".xss") || ext == _T(".rt")|| ext == _T(".txt"));
}

BOOL IsSubtitleFilename(CString filename)
{
    CString ext = CPath(filename).GetExtension().MakeLower();
    return IsSubtitleExtension(ext);
}

bool CMainFrame::IsAudioFilename(CString filename)
{
    CString ext = CPath(filename).GetExtension();
    return IsAudioFileExt(ext);
}

void CMainFrame::OnDropFiles(CAtlList<CStringW>& slFiles, DROPEFFECT dropEffect)
{
    SetForegroundWindow();

    if (slFiles.IsEmpty()) {
        return;
    }

    if (slFiles.GetCount() == 1 && OpenBD(slFiles.GetHead())) {
        return;
    }

    PathUtils::ParseDirs(slFiles);

    bool bAppend = !!(dropEffect & DROPEFFECT_APPEND);

    // Check for subtitle files
    SubtitleInput subInputSelected;
    CString subfile;
    BOOL onlysubs = true;
    BOOL subloaded = false;
    BOOL canLoadSub = !bAppend && !m_fAudioOnly && GetLoadState() == MLS::LOADED && !IsPlaybackCaptureMode();
    BOOL canLoadSubISR = canLoadSub && m_pCAP && (!m_pDVS || AfxGetAppSettings().IsISRAutoLoadEnabled());
    POSITION pos = slFiles.GetHeadPosition();
    while (pos) {
        SubtitleInput subInput;
        POSITION curpos = pos;
        subfile = slFiles.GetNext(pos);
        if (IsSubtitleFilename(subfile)) {
            // remove subtitle file from list
            slFiles.RemoveAt(curpos);
            // try to load it
            if (onlysubs && canLoadSub) {
                if (canLoadSubISR && LoadSubtitle(subfile, &subInput, False)) {
                    if (!subInputSelected.pSubStream) {
                        // first one
                        subInputSelected = subInput;
                    }
                    subloaded = true;
                } else if (m_pDVS && slFiles.IsEmpty()) {
                    if (SUCCEEDED(m_pDVS->put_FileName((LPWSTR)(LPCWSTR)subfile))) {
                        m_pDVS->put_SelectedLanguage(0);
                        m_pDVS->put_HideSubtitles(true);
                        m_pDVS->put_HideSubtitles(false);
                        subloaded = true;
                    }
                }
            }
        }
        else {
            onlysubs = false;
        }
    }

    if (onlysubs) {
        if (subInputSelected.pSubStream) {
            AfxGetAppSettings().fEnableSubtitles = true;
            SetSubtitle(subInputSelected);
        }
        if (subloaded) {
            CPath fn(subfile);
            fn.StripPath();
            CString statusmsg(static_cast<LPCTSTR>(fn));
            SendStatusMessage(statusmsg + ResStr(IDS_SUB_LOADED_SUCCESS), 3000);
        } else {
            SendStatusMessage(_T("Failed to load subtitle file"), 3000, true);
        }
        return;
    }

    if (GetMediaState() == State_Running) {
        MediaControlPause(true);
    }

    // load http url with youtube-dl, if available
    if (CanSendToYoutubeDL(slFiles.GetHead())) {
        if (!CloseMediaBeforeOpen()) {
            return;
        }
        if (ProcessYoutubeDLURL(slFiles.GetHead(), bAppend)) {
            if (!bAppend) {
                OpenCurPlaylistItem();
            }
            return;
        } else if (IsOnYDLWhitelist(slFiles.GetHead())) {
            m_closingmsg = L"Failed to extract stream URL with yt-dlp/youtube-dl";
            m_wndStatusBar.SetStatusMessage(m_closingmsg);
            // don't bother trying to open this website URL directly
            return;
        }
    }

    // add remaining items
    if (bAppend) {
        m_wndPlaylistBar.Append(slFiles, true);
    } else {
        m_wndPlaylistBar.Open(slFiles, true);
        PostMessage(WM_MPC_OPENCURPLAYLIST, 0, 0);
    }
}

void CMainFrame::OnFileSaveAs()
{
    CString in, out, ext;
    CAppSettings& s = AfxGetAppSettings();

    CPlaylistItem pli;
    if (m_wndPlaylistBar.GetCur(pli, true)) {
        in = pli.m_fns.GetHead();
    } else {
        return;
    }

    if (pli.m_bYoutubeDL || PathUtils::IsURL(in)) {
        // URL
        if (pli.m_bYoutubeDL) {
            out = _T("%(title)s.%(ext)s");
        } else {
            out = _T("choose_a_filename");
        }
    } else {
        out = PathUtils::StripPathOrUrl(in);
        ext = CPath(out).GetExtension().MakeLower();
        if (ext == _T(".cda")) {
            out = out.Left(out.GetLength() - 4) + _T(".wav");
        } else if (ext == _T(".ifo")) {
            out = out.Left(out.GetLength() - 4) + _T(".vob");
        }
    }

    if (!pli.m_bYoutubeDL || pli.m_ydlSourceURL.IsEmpty() || (AfxGetAppSettings().sYDLCommandLine.Find(_T("-o ")) < 0)) {
        CFileDialog fd(FALSE, 0, out,
                       OFN_EXPLORER | OFN_ENABLESIZING | OFN_HIDEREADONLY | OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_NOCHANGEDIR,
                       ResStr(IDS_ALL_FILES_FILTER), GetModalParent(), 0);
        if (DoFileDialogWithLastFolder(fd, s.lastFileSaveCopyPath) != IDOK || !in.CompareNoCase(fd.GetPathName())) {
            return;
        } else {
            out = fd.GetPathName();
        }
    }

    if (pli.m_bYoutubeDL && !pli.m_ydlSourceURL.IsEmpty()) {
        DownloadWithYoutubeDL(pli.m_ydlSourceURL, out);
        return;
    }

    CPath p(out);
    if (!ext.IsEmpty()) {
        p.AddExtension(ext);
    }

    OAFilterState fs = State_Stopped;
    if (m_pMC) {
        m_pMC->GetState(0, &fs);
        if (fs == State_Running) {
            MediaControlPause(true);
        }
    }

    CSaveDlg dlg(in, p);
    dlg.DoModal();

    if (m_pMC && fs == State_Running) {
        MediaControlRun();
    }
}

void CMainFrame::OnUpdateFileSaveAs(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && GetPlaybackMode() == PM_FILE);
}

bool CMainFrame::GetDIB(BYTE** ppData, long& size, bool fSilent)
{
    if (!ppData) {
        return false;
    }
    if (GetLoadState() != MLS::LOADED || m_fAudioOnly) {
        return false;
    }
    OAFilterState fs = GetMediaState();
    if (fs != State_Paused && fs != State_Running) {
        return false;
    }

    *ppData = nullptr;
    size = 0;

    if (fs == State_Running && !m_pCAP) {
        MediaControlPause(true); // wait for completion
    }

    HRESULT hr = S_OK;
    CString errmsg;

    do {
        if (m_pCAP) {
            hr = m_pCAP->GetDIB(nullptr, (DWORD*)&size);
            if (FAILED(hr)) {
                errmsg.Format(IDS_GETDIB_FAILED, hr);
                break;
            }

            *ppData = DEBUG_NEW BYTE[size];
            if (!(*ppData)) {
                return false;
            }

            hr = m_pCAP->GetDIB(*ppData, (DWORD*)&size);
            if (FAILED(hr)) {
                errmsg.Format(IDS_GETDIB_FAILED, hr);
                break;
            }
        } else if (m_pMFVDC) {
            // Capture with EVR
            BITMAPINFOHEADER bih = {sizeof(BITMAPINFOHEADER)};
            BYTE* pDib;
            DWORD dwSize;
            REFERENCE_TIME rtImage = 0;
            hr = m_pMFVDC->GetCurrentImage(&bih, &pDib, &dwSize, &rtImage);
            if (FAILED(hr) || dwSize == 0) {
                errmsg.Format(IDS_GETCURRENTIMAGE_FAILED, hr);
                break;
            }

            size = (long)dwSize + sizeof(BITMAPINFOHEADER);
            *ppData = DEBUG_NEW BYTE[size];
            if (!(*ppData)) {
                return false;
            }
            memcpy_s(*ppData, size, &bih, sizeof(BITMAPINFOHEADER));
            memcpy_s(*ppData + sizeof(BITMAPINFOHEADER), size - sizeof(BITMAPINFOHEADER), pDib, dwSize);
            CoTaskMemFree(pDib);
        } else {
            hr = m_pBV->GetCurrentImage(&size, nullptr);
            if (FAILED(hr) || size == 0) {
                errmsg.Format(IDS_GETCURRENTIMAGE_FAILED, hr);
                break;
            }

            *ppData = DEBUG_NEW BYTE[size];
            if (!(*ppData)) {
                return false;
            }

            hr = m_pBV->GetCurrentImage(&size, (long*)*ppData);
            if (FAILED(hr)) {
                errmsg.Format(IDS_GETCURRENTIMAGE_FAILED, hr);
                break;
            }
        }
    } while (0);

    if (!fSilent) {
        if (!errmsg.IsEmpty()) {
            AfxMessageBox(errmsg, MB_OK);
        }
    }

    if (fs == State_Running && GetMediaState() != State_Running) {
        MediaControlRun();
    }

    if (FAILED(hr)) {
        SAFE_DELETE_ARRAY(*ppData);
        return false;
    }

    return true;
}

#if MPC_SMTC_VIDEO_THUMBNAIL
// Callback for stb_image_write to append to vector
static void stbi_write_to_vector(void* context, void* data, int size) {
    std::vector<BYTE>* vec = (std::vector<BYTE>*)context;
    size_t oldSize = vec->size();
    vec->resize(oldSize + size);
    memcpy(vec->data() + oldSize, data, size);
}
#endif

BYTE* CMainFrame::ConvertDIBTo24bppRGB(BYTE* pData, long size, int& outWidth, int& outHeight, int& outPitch)
{
    PBITMAPINFO bi = reinterpret_cast<PBITMAPINFO>(pData);
    PBITMAPINFOHEADER bih = &bi->bmiHeader;
    int bpp = bih->biBitCount;

    if (bpp != 16 && bpp != 24 && bpp != 32) {
        return nullptr;
    }

    bool topdown = (bih->biHeight < 0);
    int w = bih->biWidth;
    int h = abs(bih->biHeight);
    int srcpitch = w * (bpp >> 3);
    int dstpitch = (w * 3 + 3) / 4 * 4; // round w * 3 to next multiple of 4

    BYTE* p = DEBUG_NEW BYTE[dstpitch * h];
    const BYTE* src = pData + sizeof(*bih);

    if (topdown) {
        BitBltFromRGBToRGB(w, h, p, dstpitch, 24, (BYTE*)src, srcpitch, bpp);
    } else {
        BitBltFromRGBToRGB(w, h, p, dstpitch, 24, (BYTE*)src + srcpitch * (h - 1), -srcpitch, bpp);
    }

    outWidth = w;
    outHeight = h;
    outPitch = dstpitch;
    return p;
}

void CMainFrame::SaveDIB(LPCTSTR fn, BYTE* pData, long size)
{
    CPath path(fn);

    int w, h, dstpitch;
    BYTE* p = ConvertDIBTo24bppRGB(pData, size, w, h, dstpitch);
    if (!p) {
        AfxMessageBox(IDS_SCREENSHOT_ERROR, MB_ICONWARNING | MB_OK, 0);
        return;
    }

    {
        Gdiplus::GdiplusStartupInput gdiplusStartupInput;
        ULONG_PTR gdiplusToken;
        Gdiplus::GdiplusStartup(&gdiplusToken, &gdiplusStartupInput, nullptr);

        Gdiplus::Bitmap* bm = new Gdiplus::Bitmap(w, h, dstpitch, PixelFormat24bppRGB, p);

        UINT num;       // number of image encoders
        UINT arraySize; // size, in bytes, of the image encoder array

        // How many encoders are there?
        // How big (in bytes) is the array of all ImageCodecInfo objects?
        Gdiplus::GetImageEncodersSize(&num, &arraySize);

        // Create a buffer large enough to hold the array of ImageCodecInfo
        // objects that will be returned by GetImageEncoders.
        Gdiplus::ImageCodecInfo* pImageCodecInfo = (Gdiplus::ImageCodecInfo*)DEBUG_NEW BYTE[arraySize];

        // GetImageEncoders creates an array of ImageCodecInfo objects
        // and copies that array into a previously allocated buffer.
        // The third argument, imageCodecInfos, is a pointer to that buffer.
        Gdiplus::GetImageEncoders(num, arraySize, pImageCodecInfo);

        Gdiplus::EncoderParameters* pEncoderParameters = nullptr;

        // Find the mime type based on the extension
        CString ext(path.GetExtension());
        CStringW mime;
        if (ext == _T(".jpg")) {
            mime = L"image/jpeg";

            // Set the encoder parameter for jpeg quality
            pEncoderParameters = DEBUG_NEW Gdiplus::EncoderParameters;
            ULONG quality = AfxGetAppSettings().nJpegQuality;

            pEncoderParameters->Count = 1;
            pEncoderParameters->Parameter[0].Guid = Gdiplus::EncoderQuality;
            pEncoderParameters->Parameter[0].Type = Gdiplus::EncoderParameterValueTypeLong;
            pEncoderParameters->Parameter[0].NumberOfValues = 1;
            pEncoderParameters->Parameter[0].Value = &quality;
        } else if (ext == _T(".bmp")) {
            mime = L"image/bmp";
        } else {
            mime = L"image/png";
        }

        // Get the encoder clsid
        CLSID encoderClsid = CLSID_NULL;
        for (UINT i = 0; i < num && encoderClsid == CLSID_NULL; i++) {
            if (wcscmp(pImageCodecInfo[i].MimeType, mime) == 0) {
                encoderClsid = pImageCodecInfo[i].Clsid;
            }
        }

        Gdiplus::Status s = bm->Save(fn, &encoderClsid, pEncoderParameters);

        // All GDI+ objects must be destroyed before GdiplusShutdown is called
        delete bm;
        delete [] pImageCodecInfo;
        delete pEncoderParameters;
        Gdiplus::GdiplusShutdown(gdiplusToken);
        delete [] p;

        if (s != Gdiplus::Ok) {
            AfxMessageBox(IDS_SCREENSHOT_ERROR, MB_ICONWARNING | MB_OK, 0);
            return;
        }
    }

    path.m_strPath.Replace(_T("\\\\"), _T("\\"));

    SendStatusMessage(m_wndStatusBar.PreparePathStatusMessage(path), 3000);
}

#if MPC_SMTC_VIDEO_THUMBNAIL
bool CMainFrame::CaptureVideoThumbnail(std::vector<BYTE>& thumbnail)
{
    // Get the current video frame as DIB
    std::vector<BYTE> dib;
    CString errmsg;
    HRESULT hr = GetCurrentFrame(dib, errmsg);
    if (FAILED(hr) || dib.empty()) {
        return false;
    }

    // Convert DIB to 24bpp BGR
    int w, h, dstpitch;
    BYTE* bgr = ConvertDIBTo24bppRGB(dib.data(), (long)dib.size(), w, h, dstpitch);
    if (!bgr) {
        return false;
    }

    // Downscale to at most 320 pixels wide, preserving aspect ratio
    int tw = w;
    int th = h;
    if (tw > 320) {
        th = std::max(1, MulDiv(h, 320, w));
        tw = 320;
    }

    // Allocate buffer for RGB output (tightly packed, no padding)
    int rgbPitch = tw * 3;
    BYTE* rgb = DEBUG_NEW BYTE[rgbPitch * th];

    // Downscale and convert BGR to RGB using stb_image_resize2
    STBIR_RESIZE resize;
    stbir_resize_init(&resize, bgr, w, h, dstpitch, rgb, tw, th, rgbPitch, STBIR_BGR, STBIR_TYPE_UINT8);
    stbir_set_pixel_layouts(&resize, STBIR_BGR, STBIR_RGB);
    stbir_resize_extended(&resize);

    delete[] bgr;

    // Encode to JPEG using stb_image_write
    int quality = AfxGetAppSettings().nJpegQuality;
    int result = stbi_write_jpg_to_func(stbi_write_to_vector, &thumbnail, tw, th, 3, rgb, quality);

    delete[] rgb;
    return result != 0;
}
#endif

HRESULT GetBasicVideoFrame(IBasicVideo* pBasicVideo, std::vector<BYTE>& dib) {
    // IBasicVideo::GetCurrentImage() gives the original frame

    long size;

    HRESULT hr = pBasicVideo->GetCurrentImage(&size, nullptr);
    if (FAILED(hr)) {
        return hr;
    }
    if (size <= 0) {
        return E_ABORT;
    }

    dib.resize(size);

    hr = pBasicVideo->GetCurrentImage(&size, (long*)dib.data());
    if (FAILED(hr)) {
        dib.clear();
    }

    return hr;
}

HRESULT GetVideoDisplayControlFrame(IMFVideoDisplayControl* pVideoDisplayControl, std::vector<BYTE>& dib) {
    // IMFVideoDisplayControl::GetCurrentImage() gives the displayed frame

    BITMAPINFOHEADER	bih = { sizeof(BITMAPINFOHEADER) };
    BYTE* pDib;
    DWORD				size;
    REFERENCE_TIME		rtImage = 0;

    HRESULT hr = pVideoDisplayControl->GetCurrentImage(&bih, &pDib, &size, &rtImage);
    if (S_OK != hr) {
        return hr;
    }
    if (size == 0) {
        return E_ABORT;
    }

    dib.resize(sizeof(BITMAPINFOHEADER) + size);

    memcpy(dib.data(), &bih, sizeof(BITMAPINFOHEADER));
    memcpy(dib.data() + sizeof(BITMAPINFOHEADER), pDib, size);
    CoTaskMemFree(pDib);

    return hr;
}

HRESULT GetMadVRFrameGrabberFrame(IMadVRFrameGrabber* pMadVRFrameGrabber, std::vector<BYTE>& dib, bool displayed) {
    LPVOID dibImage = nullptr;
    HRESULT hr;

    if (displayed) {
        hr = pMadVRFrameGrabber->GrabFrame(ZOOM_PLAYBACK_SIZE, 0, 0, 0, 0, 0, &dibImage, 0);
    } else {
        hr = pMadVRFrameGrabber->GrabFrame(ZOOM_ENCODED_SIZE, 0, 0, 0, 0, 0, &dibImage, 0);
    }

    if (S_OK != hr) {
        return hr;
    }
    if (!dibImage) {
        return E_ABORT;
    }

    const BITMAPINFOHEADER* bih = (BITMAPINFOHEADER*)dibImage;

    dib.resize(sizeof(BITMAPINFOHEADER) + bih->biSizeImage);
    memcpy(dib.data(), dibImage, sizeof(BITMAPINFOHEADER) + bih->biSizeImage);
    LocalFree(dibImage);

    return hr;
}

HRESULT CMainFrame::GetDisplayedImage(std::vector<BYTE>& dib, CString& errmsg) {
    errmsg.Empty();
    HRESULT hr;

	if (m_pCAP) {
		LPVOID dibImage = nullptr;
		hr = m_pCAP->GetDisplayedImage(&dibImage);

		if (S_OK == hr && dibImage) {
			const BITMAPINFOHEADER* bih = (BITMAPINFOHEADER*)dibImage;
			dib.resize(sizeof(BITMAPINFOHEADER) + bih->biSizeImage);
			memcpy(dib.data(), dibImage, sizeof(BITMAPINFOHEADER) + bih->biSizeImage);
			LocalFree(dibImage);
		}
	}
	else if (m_pMFVDC) {
        hr = GetVideoDisplayControlFrame(m_pMFVDC, dib);
    } else if (m_pMVRFG) {
        hr = GetMadVRFrameGrabberFrame(m_pMVRFG, dib, true);
    } else {
        hr = E_NOINTERFACE;
    }

    if (FAILED(hr)) {
		errmsg.Format(L"CMainFrame::GetCurrentImage() failed, 0x%08x", hr);
    }

    return hr;
}

HRESULT CMainFrame::GetCurrentFrame(std::vector<BYTE>& dib, CString& errmsg) {
    HRESULT hr = S_OK;
    errmsg.Empty();

    OAFilterState fs = GetMediaState();
    if (m_eMediaLoadState != MLS::LOADED || m_fAudioOnly || (fs != State_Paused && fs != State_Running)) {
        return E_ABORT;
    }

    if (fs == State_Running && !m_pCAP) {
        MediaControlPause(true); //wait for completion
    }

    if (m_pCAP) {
        DWORD size;
        hr = m_pCAP->GetDIB(nullptr, &size);

        if (S_OK == hr) {
            dib.resize(size);
            hr = m_pCAP->GetDIB(dib.data(), &size);
        }

        if (FAILED(hr)) {
            errmsg.Format(L"ISubPicAllocatorPresenter3::GetDIB() failed, 0x%08x", hr);
        }
    } else if (m_pBV) {
        hr = GetBasicVideoFrame(m_pBV, dib);

        if (hr == E_NOINTERFACE && m_pMFVDC) {
            // hmm, EVR is not able to give the original frame, giving the displayed image
            hr = GetDisplayedImage(dib, errmsg);
        } else if (FAILED(hr)) {
            errmsg.Format(L"IBasicVideo::GetCurrentImage() failed, 0x%08x", hr);
        }
    } else {
        hr = E_POINTER;
        errmsg.Format(L"Interface not found!");
    }

    if (fs == State_Running && GetMediaState() != State_Running) {
        MediaControlRun();
    }

    return hr;
}

HRESULT CMainFrame::GetOriginalFrame(std::vector<BYTE>& dib, CString& errmsg) {
    HRESULT hr = S_OK;
    errmsg.Empty();

    if (m_pMVRFG) {
        hr = GetMadVRFrameGrabberFrame(m_pMVRFG, dib, false);
        if (FAILED(hr)) {
            errmsg.Format(L"IMadVRFrameGrabber::GrabFrame() failed, 0x%08x", hr);
        }
    } else {
        hr = GetCurrentFrame(dib, errmsg);
    }

    return hr;
}

HRESULT CMainFrame::RenderCurrentSubtitles(BYTE* pData) {
    ASSERT(m_pCAP && AfxGetAppSettings().bSnapShotSubtitles && !m_pMVRFG && AfxGetAppSettings().fEnableSubtitles && AfxGetAppSettings().IsISRAutoLoadEnabled());
    CheckPointer(pData, E_FAIL);
    HRESULT hr = S_FALSE;

    if (CComQIPtr<ISubPicProvider> pSubPicProvider = m_pCurrentSubInput.pSubStream) {
        const PBITMAPINFOHEADER bih = (PBITMAPINFOHEADER)pData;
        const int width = bih->biWidth;
        const int height = abs(bih->biHeight);
        const bool topdown = bih->biHeight < 0;

        REFERENCE_TIME rtNow = 0;
        m_pMS->GetCurrentPosition(&rtNow);

        int delay = m_pCAP->GetSubtitleDelay();
        if (delay != 0) {
            if (delay > 0 && delay * 10000LL > rtNow) {
                return S_FALSE;
            } else {
                rtNow -= delay * 10000LL;
            }
        }

        int subWidth = width;
        int subHeight = height;
        bool needsResize = false;
        if (CPGSSub* pgsSub = dynamic_cast<CPGSSub*>(pSubPicProvider.p)) {
            CSize sz;
            if (SUCCEEDED(pgsSub->GetPresentationSegmentTextureSize(rtNow, sz))) {
                subWidth = sz.cx;
                subHeight = sz.cy;
                needsResize = true;
            }
        }

        SubPicDesc spdRender;
        
        spdRender.type = MSP_RGB32;
        spdRender.w = subWidth;
        spdRender.h = subHeight;
        spdRender.bpp = 32;
        spdRender.pitch = subWidth * 4;
        spdRender.vidrect = { 0, 0, width, height };
        spdRender.bits = DEBUG_NEW BYTE[spdRender.pitch * spdRender.h];
        
        CComPtr<CMemSubPicAllocator> pSubPicAllocator = DEBUG_NEW CMemSubPicAllocator(spdRender.type, CSize(spdRender.w, spdRender.h));

        CMemSubPic memSubPic(spdRender, pSubPicAllocator);
        memSubPic.SetInverseAlpha(false);
        memSubPic.ClearDirtyRect();

        RECT bbox = {};
        hr = pSubPicProvider->Render(spdRender, rtNow, m_pCAP->GetFPS(), bbox);
        if (needsResize) {
            memSubPic.UnlockARGB();
        }

        if (S_OK == hr) {
            SubPicDesc spdTarget;
            spdTarget.type = MSP_RGB32;
            spdTarget.w = width;
            spdTarget.h = height;
            spdTarget.bpp = 32;
            spdTarget.pitch = topdown ? width * 4 : -width * 4;
            spdTarget.vidrect = { 0, 0, width, height };
            spdTarget.bits = (BYTE*)(bih + 1) + (topdown ? 0 : (width * 4) * (height - 1));

            hr = memSubPic.AlphaBlt(&spdRender.vidrect, &spdTarget.vidrect, &spdTarget);
        }
    }

    return hr;
}

void CMainFrame::SaveImage(LPCWSTR fn, bool displayed, bool includeSubtitles) {
    std::vector<BYTE> dib;
    CString errmsg;
    HRESULT hr;
    if (displayed) {
        hr = GetDisplayedImage(dib, errmsg);
    } else {
        hr = GetCurrentFrame(dib, errmsg);
        if (includeSubtitles && m_pCAP && hr == S_OK) {
            RenderCurrentSubtitles(dib.data());
        }
    }

    if (hr == S_OK) {
        SaveDIB(fn, dib.data(), (long)dib.size());
        m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_OSD_IMAGE_SAVED), 3000);
    } else {
        m_OSD.DisplayMessage(OSD_TOPLEFT, errmsg, 3000);
    }
}

void CMainFrame::SaveThumbnails(LPCTSTR fn)
{
    if (!m_pMC || !m_pMS || GetPlaybackMode() != PM_FILE /*&& GetPlaybackMode() != PM_DVD*/) {
        return;
    }

    REFERENCE_TIME rtPos = GetPos();
    REFERENCE_TIME rtDur = GetDur();

    if (rtDur <= 0) {
        AfxMessageBox(IDS_THUMBNAILS_NO_DURATION, MB_ICONWARNING | MB_OK, 0);
        return;
    }

    OAFilterState filterState = UpdateCachedMediaState();
    bool bWasStopped = (filterState == State_Stopped);
    if (filterState != State_Paused) {
        OnPlayPause();
    }

    CSize szVideoARCorrected, szVideo, szAR;

    if (m_pCAP) {
        szVideo = m_pCAP->GetVideoSize(false);
        szAR = m_pCAP->GetVideoSize(true);
    } else if (m_pMFVDC) {
        VERIFY(SUCCEEDED(m_pMFVDC->GetNativeVideoSize(&szVideo, &szAR)));
    } else {
        VERIFY(SUCCEEDED(m_pBV->GetVideoSize(&szVideo.cx, &szVideo.cy)));

        CComQIPtr<IBasicVideo2> pBV2 = m_pBV;
        long lARx = 0, lARy = 0;
        if (pBV2 && SUCCEEDED(pBV2->GetPreferredAspectRatio(&lARx, &lARy)) && lARx > 0 && lARy > 0) {
            szAR.SetSize(lARx, lARy);
        }
    }

    if (szVideo.cx <= 0 || szVideo.cy <= 0) {
        AfxMessageBox(IDS_THUMBNAILS_NO_FRAME_SIZE, MB_ICONWARNING | MB_OK, 0);
        return;
    }

    // with the overlay mixer IBasicVideo2 won't tell the new AR when changed dynamically
    DVD_VideoAttributes VATR;
    if (GetPlaybackMode() == PM_DVD && SUCCEEDED(m_pDVDI->GetCurrentVideoAttributes(&VATR))) {
        szAR.SetSize(VATR.ulAspectX, VATR.ulAspectY);
    }

    szVideoARCorrected = (szAR.cx <= 0 || szAR.cy <= 0) ? szVideo : CSize(MulDiv(szVideo.cy, szAR.cx, szAR.cy), szVideo.cy);

    const CAppSettings& s = AfxGetAppSettings();

    int cols = std::clamp(s.iThumbCols, 1, 16);
    int rows = std::clamp(s.iThumbRows, 1, 40);

    const int margin = 5;
    int width = std::clamp(s.iThumbWidth, 256, 3840);
    double fontscale = width / 1280.0;
    int fontsize = (int)(fontscale * 16);
    const int infoheight = 4 * fontsize + 6 + 2 * margin;
    int height = width * szVideoARCorrected.cy / szVideoARCorrected.cx * rows / cols + infoheight;

    int dibsize = sizeof(BITMAPINFOHEADER) + width * height * 4;

    CAutoVectorPtr<BYTE> dib;
    if (!dib.Allocate(dibsize)) {
        AfxMessageBox(IDS_OUT_OF_MEMORY, MB_ICONWARNING | MB_OK, 0);
        return;
    }

    BITMAPINFOHEADER* bih = (BITMAPINFOHEADER*)(BYTE*)dib;
    ZeroMemory(bih, sizeof(BITMAPINFOHEADER));
    bih->biSize = sizeof(BITMAPINFOHEADER);
    bih->biWidth = width;
    bih->biHeight = height;
    bih->biPlanes = 1;
    bih->biBitCount = 32;
    bih->biCompression = BI_RGB;
    bih->biSizeImage = width * height * 4;
    memsetd(bih + 1, 0xffffff, bih->biSizeImage);

    SubPicDesc spd;
    spd.w = width;
    spd.h = height;
    spd.bpp = 32;
    spd.pitch = -width * 4;
    spd.vidrect = CRect(0, 0, width, height);
    spd.bits = (BYTE*)(bih + 1) + (width * 4) * (height - 1);

    bool darktheme = s.bMPCTheme && s.eModernThemeMode == CMPCTheme::ModernThemeMode::DARK;

    int gradientBase = 0xe0;
    if (darktheme) {
        gradientBase = 0x00;
    }
    // Paint the background
    {
        BYTE* p = (BYTE*)spd.bits;
        for (int y = 0; y < spd.h; y++, p += spd.pitch) {
            for (int x = 0; x < spd.w; x++) {
                ((DWORD*)p)[x] = 0x010101 * (gradientBase + 0x08 * y / spd.h + 0x18 * (spd.w - x) / spd.w);
            }
        }
    }

    CCritSec csSubLock;
    RECT bbox;
    CSize szThumbnail((width - margin * 2) / cols - margin * 2, (height - margin * 2 - infoheight) / rows - margin * 2);
    // Ensure the thumbnails aren't ridiculously small so that the time indication can at least fit
    if (szThumbnail.cx < 60 || szThumbnail.cy < 20) {
        AfxMessageBox(IDS_THUMBNAIL_TOO_SMALL, MB_ICONWARNING | MB_OK, 0);
        return;
    }

    m_nVolumeBeforeFrameStepping = m_wndToolBar.Volume;
    if (m_pBA) {
        m_pBA->put_Volume(-10000);
    }

    // Draw the thumbnails
    std::unique_ptr<BYTE[]> thumb(new(std::nothrow) BYTE[szThumbnail.cx * szThumbnail.cy * 4]);
    if (!thumb) {
        return;
    }

    int pics = cols * rows;
    REFERENCE_TIME rtInterval = rtDur / (pics + 1LL);
    for (int i = 1; i <= pics; i++) {
        REFERENCE_TIME rt = rtInterval * i;
        // use a keyframe if close to target time
        if (rtInterval >= 100000000LL) {
            REFERENCE_TIME rtMaxDiff = std::min(100000000LL, rtInterval / 10); // no more than 10 sec
            rt = GetClosestKeyFrame(rt, rtMaxDiff, rtMaxDiff);
        }

        DoSeekTo(rt, false);
        UpdateWindow();

        HRESULT hr = m_pFS ? m_pFS->Step(1, nullptr) : E_FAIL;
        if (FAILED(hr)) {
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
            AfxMessageBox(IDS_FRAME_STEP_ERROR_RENDERER, MB_ICONEXCLAMATION | MB_OK, 0);
            return;
        }

        bool abortloop = false;
        HANDLE hGraphEvent = nullptr;
        m_pME->GetEventHandle((OAEVENT*)&hGraphEvent);
        while (hGraphEvent) {
            DWORD res = WaitForSingleObject(hGraphEvent, 5000);
            if (res == WAIT_OBJECT_0) {
                LONG evCode = 0;
                LONG_PTR evParam1, evParam2;
                while (m_pME && SUCCEEDED(m_pME->GetEvent(&evCode, &evParam1, &evParam2, 0))) {
                    m_pME->FreeEventParams(evCode, evParam1, evParam2);
                    if (EC_STEP_COMPLETE == evCode) {
                        hGraphEvent = nullptr;
                    }
                }
            } else {
                hGraphEvent = nullptr;
                if (res == WAIT_TIMEOUT) {
                    // Likely a seek failure has occurred. For example due to an incomplete file.
                    REFERENCE_TIME rtCur = 0;
                    m_pMS->GetCurrentPosition(&rtCur);
                    if (rtCur >= rtDur) {
                        abortloop = true;
                    }
                }
            }
        }

        if (abortloop) {
            break;
        }

        int col = (i - 1) % cols;
        int row = (i - 1) / cols;

        CPoint p(2 * margin + col * (szThumbnail.cx + 2 * margin), infoheight + 2 * margin + row * (szThumbnail.cy + 2 * margin));
        CRect r(p, szThumbnail);

        CRenderedTextSubtitle rts(&csSubLock);
        rts.m_SubRendererSettings.renderSSAUsingLibass = false;
        rts.m_SubRendererSettings.overrideDefaultStyle = false;
        rts.m_SubRendererSettings.overrideAllStyles = false;
        rts.CreateDefaultStyle(0);
        rts.m_storageRes = rts.m_playRes = CSize(width, height);
        STSStyle* style = DEBUG_NEW STSStyle();
        style->fontName = L"Calibri";
        style->marginRect.SetRectEmpty();
        rts.AddStyle(_T("thumbs"), style);

        DVD_HMSF_TIMECODE hmsf = RT2HMS_r(rt);
        CStringW str;
        if (!darktheme) {
            str.Format(L"{\\an7\\1c&Hffffff&\\4a&Hb0&\\bord1\\shad4\\be1}{\\p1}m %d %d l %d %d %d %d %d %d{\\p}",
                r.left, r.top, r.right, r.top, r.right, r.bottom, r.left, r.bottom);
            rts.Add(str, true, MS2RT(0), MS2RT(1), _T("thumbs")); // Thumbnail background
        }
        str.Format(L"{\\an3\\1c&Hffffff&\\3c&H000000&\\alpha&H80&\\fs%d\\b1\\bord2\\shad0\\pos(%d,%d)}%02u:%02u:%02u",
                   fontsize, r.right - 5, r.bottom - 3, hmsf.bHours, hmsf.bMinutes, hmsf.bSeconds);
        rts.Add(str, true, MS2RT(1), MS2RT(2), _T("thumbs")); // Thumbnail time

        rts.Render(spd, 0, 25, bbox); // Draw the thumbnail background/time

        BYTE* pData = nullptr;
        long size = 0;
        if (!GetDIB(&pData, size)) {
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
            return;
        }

        BITMAPINFO* bi = (BITMAPINFO*)pData;

        if (bi->bmiHeader.biBitCount != 32) {
            CString strTemp;
            strTemp.Format(IDS_THUMBNAILS_INVALID_FORMAT, bi->bmiHeader.biBitCount);
            AfxMessageBox(strTemp);
            delete [] pData;
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
            return;
        }

        int sw = bi->bmiHeader.biWidth;
        int sh = abs(bi->bmiHeader.biHeight);
        int sp = sw * 4;
        const BYTE* src = pData + sizeof(bi->bmiHeader);

        stbir_resize(src, sw, sh, sp, thumb.get(), szThumbnail.cx, szThumbnail.cy, szThumbnail.cx * 4, STBIR_RGBA_PM, STBIR_TYPE_UINT8, STBIR_EDGE_CLAMP, STBIR_FILTER_DEFAULT);

        BYTE* dst = spd.bits + spd.pitch * r.top + r.left * 4;

        const BYTE* tsrc = thumb.get();
        int tsrcPitch = szThumbnail.cx * 4;
        if (bi->bmiHeader.biHeight >= 0) {
            tsrc += tsrcPitch * (szThumbnail.cy - 1);
            tsrcPitch = -tsrcPitch;
        }
        for (int y = 0; y < szThumbnail.cy; y++, dst += spd.pitch, tsrc += tsrcPitch) {
            memcpy(dst, tsrc, abs(tsrcPitch));
        }
        
        rts.Render(spd, 10000, 25, bbox); // Draw the thumbnail time

        delete [] pData;
    }

    // Draw the file information
    {
        CRenderedTextSubtitle rts(&csSubLock);
        rts.m_SubRendererSettings.renderSSAUsingLibass = false;
        rts.m_SubRendererSettings.overrideDefaultStyle = false;
        rts.m_SubRendererSettings.overrideAllStyles = false;
        rts.CreateDefaultStyle(0);
        rts.m_storageRes = rts.m_playRes = CSize(width, height);
        STSStyle* style = DEBUG_NEW STSStyle();
        // Use System UI font.
        CFont tempFont;
        CMPCThemeUtil::getFontByType(tempFont, nullptr, CMPCThemeUtil::MessageFont);
        LOGFONT lf;
        if (tempFont.GetLogFont(&lf)) {
            CString fontName(lf.lfFaceName);
            style->fontName = fontName;
        }
        style->marginRect.SetRect(margin * 2, margin * 2, margin * 2, height - infoheight - margin);
        rts.AddStyle(_T("thumbs"), style);

        CStringW str;
        str.Format(L"{\\an9\\fs%d\\b1\\bord0\\shad0\\1c&Hffffff&}%s", infoheight - 2 * margin, L"MPC-HC");
        if (darktheme) {
            str.Replace(L"\\1c&Hffffff", L"\\1c&Hc8c8c8");
        }
        rts.Add(str, true, 0, 1, _T("thumbs"), _T(""), _T(""), CRect(0, 0, 0, 0), -1);

        DVD_HMSF_TIMECODE hmsf = RT2HMS_r(rtDur);

        CString title;
        CPlaylistItem pli;
        if (m_wndPlaylistBar.GetCur(pli, true) && pli.m_bYoutubeDL && pli.m_label && !pli.m_label.IsEmpty()) {
            title = pli.m_label;
        } else {
            title = GetFileName();
        }

        CStringW fs;
        CString curfile = m_wndPlaylistBar.GetCurFileName();
        if (!PathUtils::IsURL(curfile)) {
            ExtendMaxPathLengthIfNeeded(curfile, true);
            WIN32_FIND_DATA wfd;
            HANDLE hFind = FindFirstFile(curfile, &wfd);
            if (hFind != INVALID_HANDLE_VALUE) {
                FindClose(hFind);

                __int64 size = (__int64(wfd.nFileSizeHigh) << 32) | wfd.nFileSizeLow;
                const int MAX_FILE_SIZE_BUFFER = 65;
                WCHAR szFileSize[MAX_FILE_SIZE_BUFFER];
                StrFormatByteSizeW(size, szFileSize, MAX_FILE_SIZE_BUFFER);
                CString szByteSize;
                szByteSize.Format(_T("%I64d"), size);
                fs.Format(IDS_THUMBNAILS_INFO_FILESIZE, szFileSize, FormatNumber(szByteSize).GetString());
            }
        }        

        CStringW ar;
        if (szAR.cx > 0 && szAR.cy > 0 && szAR.cx != szVideo.cx && szAR.cy != szVideo.cy) {
            ar.Format(L"(%ld:%ld)", szAR.cx, szAR.cy);
        }
        CStringW fmt = ResStr(IDS_THUMBNAILS_INFO_HEADER);
        if (darktheme) {
            fmt.Replace(L"\\1c&H000000", L"\\1c&Hc8c8c8");
        }
        str.Format(fmt, fontsize,
                   title.GetString(), fs.GetString(), szVideo.cx, szVideo.cy, ar.GetString(), hmsf.bHours, hmsf.bMinutes, hmsf.bSeconds);
        rts.Add(str, true, 0, 1, _T("thumbs"));

        rts.Render(spd, 0, 25, bbox);
    }

    SaveDIB(fn, (BYTE*)dib, dibsize);

    if (m_pBA) {
        m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
    }

    if (bWasStopped) {
        OnPlayStop();
    } else {
        DoSeekTo(rtPos, false);
    }

    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_OSD_THUMBS_SAVED), 3000);
}

CString CMainFrame::MakeSnapshotFileName(BOOL thumbnails)
{
    CAppSettings& s = AfxGetAppSettings();
    CString prefix;
    CString fn;

    ASSERT(!thumbnails || GetPlaybackMode() == PM_FILE);

    auto videoFn = GetFileName();
    auto fullName = m_wndPlaylistBar.GetCurFileName(true);
    bool needsExtensionRemoval = !s.bSnapShotKeepVideoExtension;
    if (IsPlaylistFile(videoFn)) {
        CPlaylistItem pli;
        if (m_wndPlaylistBar.GetCur(pli, true)) {
            videoFn = pli.m_label;
            needsExtensionRemoval = false;
        }
    } else if (needsExtensionRemoval && PathUtils::IsURL(fullName)){
        auto title = getBestTitle();
        if (!title.IsEmpty()) {
            videoFn = title;
            needsExtensionRemoval = false;
        }
    }


    if (needsExtensionRemoval) {
        int nPos = videoFn.ReverseFind('.');
        if (nPos != -1) {
            videoFn = videoFn.Left(nPos);
        }
    }

    bool saveImagePosition, saveImageCurrentTime;

    if (m_wndSeekBar.HasDuration()) {
        saveImagePosition = s.bSaveImagePosition;
        saveImageCurrentTime = s.bSaveImageCurrentTime;
    } else {
        saveImagePosition = false;
        saveImageCurrentTime = true;
    }

    if (GetPlaybackMode() == PM_FILE) {
        if (thumbnails) {
            prefix.Format(_T("%s_thumbs"), videoFn.GetString());
        } else {
            if (saveImagePosition) {
                prefix.Format(_T("%s_snapshot_%s"), videoFn.GetString(), GetVidPos().GetString());
            } else {
                prefix.Format(_T("%s_snapshot"), videoFn.GetString());
            }
        }
    } else if (GetPlaybackMode() == PM_DVD) {
        if (saveImagePosition) {
            prefix.Format(_T("dvd_snapshot_%s"), GetVidPos().GetString());
        } else {
            prefix = _T("dvd_snapshot");
        }
    } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
        prefix.Format(_T("%s_snapshot"), m_pDVBState->sChannelName.GetString());
    } else {
        prefix = _T("snapshot");
    }

    if (!thumbnails && saveImageCurrentTime) {
        CTime t = CTime::GetCurrentTime();
        fn.Format(_T("%s_[%s]%s"), PathUtils::FilterInvalidCharsFromFileName(prefix).GetString(), t.Format(_T("%Y.%m.%d_%H.%M.%S")).GetString(), s.strSnapshotExt.GetString());
    } else {
        fn.Format(_T("%s%s"), PathUtils::FilterInvalidCharsFromFileName(prefix).GetString(), s.strSnapshotExt.GetString());
    }
    return fn;
}

BOOL CMainFrame::IsRendererCompatibleWithSaveImage()
{
    BOOL result = TRUE;
    const CAppSettings& s = AfxGetAppSettings();

    if (m_fShockwaveGraph) {
        AfxMessageBox(IDS_SCREENSHOT_ERROR_SHOCKWAVE, MB_ICONEXCLAMATION | MB_OK, 0);
        result = FALSE;
    } else if (s.iDSVideoRendererType == VIDRNDT_DS_OVERLAYMIXER) {
        AfxMessageBox(IDS_SCREENSHOT_ERROR_OVERLAY, MB_ICONEXCLAMATION | MB_OK, 0);
        result = FALSE;
    }

    return result;
}

CString CMainFrame::GetVidPos() const
{
    CString posstr = _T("");
    if ((GetPlaybackMode() == PM_FILE) || (GetPlaybackMode() == PM_DVD)) {
        __int64 start, stop, pos;
        m_wndSeekBar.GetRange(start, stop);
        pos = m_wndSeekBar.GetPos();

        DVD_HMSF_TIMECODE tcNow = RT2HMSF(pos);
        DVD_HMSF_TIMECODE tcDur = RT2HMSF(stop);

        if (tcDur.bHours > 0 || tcNow.bHours > 0) {
            posstr.Format(_T("%02u.%02u.%02u.%03u"), tcNow.bHours, tcNow.bMinutes, tcNow.bSeconds, (pos / 10000) % 1000);
        } else {
            posstr.Format(_T("%02u.%02u.%03u"), tcNow.bMinutes, tcNow.bSeconds, (pos / 10000) % 1000);
        }
    }

    return posstr;
}

void CMainFrame::OnFileSaveImage()
{
    CAppSettings& s = AfxGetAppSettings();

    /* Check if a compatible renderer is being used */
    if (!IsRendererCompatibleWithSaveImage()) {
        return;
    }

    CPath psrc;
    if (!s.strSnapshotPath.IsEmpty() && PathUtils::IsDir(s.strSnapshotPath)) {
        psrc.Combine(s.strSnapshotPath.GetString(), MakeSnapshotFileName(FALSE));
    } else {
        psrc = CPath(MakeSnapshotFileName(FALSE));        
    }

    bool subtitleOptionSupported = !m_pMVRFG && s.fEnableSubtitles && s.IsISRAutoLoadEnabled();

    CSaveImageDialog fd(s.nJpegQuality, s.strSnapshotExt, (LPCTSTR)psrc,
                        _T("BMP - Windows Bitmap (*.bmp)|*.bmp|JPG - JPEG Image (*.jpg)|*.jpg|PNG - Portable Network Graphics (*.png)|*.png||"), GetModalParent(), subtitleOptionSupported);

    if (s.strSnapshotExt == _T(".bmp")) {
        fd.m_pOFN->nFilterIndex = 1;
    } else if (s.strSnapshotExt == _T(".jpg")) {
        fd.m_pOFN->nFilterIndex = 2;
    } else if (s.strSnapshotExt == _T(".png")) {
        fd.m_pOFN->nFilterIndex = 3;
    }

    if (fd.DoModal() != IDOK) {
        return;
    }

    if (fd.m_pOFN->nFilterIndex == 1) {
        s.strSnapshotExt = _T(".bmp");
    } else if (fd.m_pOFN->nFilterIndex == 2) {
        s.strSnapshotExt = _T(".jpg");
        s.nJpegQuality = fd.m_nJpegQuality;
    } else {
        fd.m_pOFN->nFilterIndex = 3;
        s.strSnapshotExt = _T(".png");
    }

    CPath pdst(fd.GetPathName());
    CString ext(pdst.GetExtension().MakeLower());
    if (ext != s.strSnapshotExt) {
        if (ext == _T(".bmp") || ext == _T(".jpg") || ext == _T(".png")) {
            ext = s.strSnapshotExt;
        } else {
            ext += s.strSnapshotExt;
        }
        if (!pdst.RenameExtension(ext)) {
            ASSERT(false);
            return;
        }
    }
    CString path = (LPCTSTR)pdst;
    pdst.RemoveFileSpec();
    s.strSnapshotPath = (LPCTSTR)pdst;

    bool includeSubtitles = subtitleOptionSupported && s.bSnapShotSubtitles;

    SaveImage(path, false, includeSubtitles);
}

void CMainFrame::OnFileSaveImageAuto()
{
    const CAppSettings& s = AfxGetAppSettings();

    // If path doesn't exist, Save Image instead
    if (!PathUtils::IsDir(s.strSnapshotPath)) {
        OnFileSaveImage();
        return;
    }

    /* Check if a compatible renderer is being used */
    if (!IsRendererCompatibleWithSaveImage()) {
        return;
    }

    bool includeSubtitles = s.bSnapShotSubtitles && !m_pMVRFG && s.fEnableSubtitles && s.IsISRAutoLoadEnabled();

    CString fn;
    fn.Format(_T("%s\\%s"), s.strSnapshotPath.GetString(), MakeSnapshotFileName(FALSE).GetString());
    SaveImage(fn.GetString(), false, includeSubtitles);
}

void CMainFrame::OnUpdateFileSaveImage(CCmdUI* pCmdUI)
{
    OAFilterState fs = GetMediaState();
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && (fs == State_Paused || fs == State_Running));
}

void CMainFrame::OnCmdLineSaveThumbnails()
{
    CAppSettings& s = AfxGetAppSettings();

    /* Check if a compatible renderer is being used */
    if (!IsRendererCompatibleWithSaveImage()) {
        return;
    }

    CPlaylistItem pli;
    if (!m_wndPlaylistBar.GetCur(pli, true)) {
        return;
    }

    CPath psrc(m_wndPlaylistBar.GetCurFileName(true));
    psrc.RemoveFileSpec();
    psrc.Combine(psrc, MakeSnapshotFileName(TRUE));

    s.iThumbRows = std::clamp(s.iThumbRows, 1, 40);
    s.iThumbCols = std::clamp(s.iThumbCols, 1, 16);
    s.iThumbWidth = std::clamp(s.iThumbWidth, 256, 3840);

    CString path = (LPCTSTR)psrc;

    SaveThumbnails(path);

}

void CMainFrame::OnFileSaveThumbnails()
{
    CAppSettings& s = AfxGetAppSettings();

    /* Check if a compatible renderer is being used */
    if (!IsRendererCompatibleWithSaveImage()) {
        return;
    }

    CPath psrc(s.strSnapshotPath);
    psrc.Combine(s.strSnapshotPath, MakeSnapshotFileName(TRUE));

    CSaveThumbnailsDialog fd(s.nJpegQuality, s.iThumbRows, s.iThumbCols, s.iThumbWidth, s.strSnapshotExt, (LPCTSTR)psrc,
                             _T("BMP - Windows Bitmap (*.bmp)|*.bmp|JPG - JPEG Image (*.jpg)|*.jpg|PNG - Portable Network Graphics (*.png)|*.png||"), GetModalParent());

    if (s.strSnapshotExt == _T(".bmp")) {
        fd.m_pOFN->nFilterIndex = 1;
    } else if (s.strSnapshotExt == _T(".jpg")) {
        fd.m_pOFN->nFilterIndex = 2;
    } else if (s.strSnapshotExt == _T(".png")) {
        fd.m_pOFN->nFilterIndex = 3;
    }

    if (fd.DoModal() != IDOK) {
        return;
    }

    if (fd.m_pOFN->nFilterIndex == 1) {
        s.strSnapshotExt = _T(".bmp");
    } else if (fd.m_pOFN->nFilterIndex == 2) {
        s.strSnapshotExt = _T(".jpg");
        s.nJpegQuality = fd.m_nJpegQuality;
    } else {
        fd.m_pOFN->nFilterIndex = 3;
        s.strSnapshotExt = _T(".png");
    }

    s.iThumbRows = std::clamp(fd.m_rows, 1, 40);
    s.iThumbCols = std::clamp(fd.m_cols, 1, 16);
    s.iThumbWidth = std::clamp(fd.m_width, 256, 3840);

    CPath pdst(fd.GetPathName());
    CString ext(pdst.GetExtension().MakeLower());
    if (ext != s.strSnapshotExt) {
        if (ext == _T(".bmp") || ext == _T(".jpg") || ext == _T(".png")) {
            ext = s.strSnapshotExt;
        } else {
            ext += s.strSnapshotExt;
        }
        if (!pdst.RenameExtension(ext)) {
            // ToDo: write helper functions for renaming that support long paths
            ASSERT(false);
            return;
        }
    }
    CString path = (LPCTSTR)pdst;
    pdst.RemoveFileSpec();
    s.strSnapshotPath = (LPCTSTR)pdst;

    SaveThumbnails(path);
}

void CMainFrame::OnUpdateFileSaveThumbnails(CCmdUI* pCmdUI)
{
    OAFilterState fs = GetMediaState();
    UNREFERENCED_PARAMETER(fs);
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && (GetPlaybackMode() == PM_FILE /*|| GetPlaybackMode() == PM_DVD*/));
}

void CMainFrame::OnFileSubtitlesLoad()
{
    if (!m_pCAP && !m_pDVS) {
        AfxMessageBox(IDS_CANNOT_LOAD_SUB, MB_ICONINFORMATION | MB_OK, 0);
        return;
    }

    DWORD dwFlags = OFN_EXPLORER | OFN_ALLOWMULTISELECT | OFN_ENABLESIZING | OFN_NOCHANGEDIR;
    if (!AfxGetAppSettings().fKeepHistory) {
        dwFlags |= OFN_DONTADDTORECENT;
    }
    CString filters;
    filters.Format(_T("%s|*.srt;*.sub;*.ssa;*.ass;*.smi;*.psb;*.txt;*.idx;*.usf;*.xss;*.rt;*.sup;*.webvtt;*.vtt|%s"),
                   ResStr(IDS_SUBTITLE_FILES_FILTER).GetString(), ResStr(IDS_ALL_FILES_FILTER).GetString());

    CFileDialog fd(TRUE, nullptr, nullptr, dwFlags, filters, GetModalParent());

    OPENFILENAME& ofn = fd.GetOFN();
    // Provide a buffer big enough to hold 16 paths (which should be more than enough).
    // Only the old style dialog falls back to it, GetSelectedPaths() normally reads the
    // selection straight from the shell interface.
    const int nBufferSize = 16 * (MAX_PATH + 1) + 1;
    CString filenames;
    ofn.lpstrFile = filenames.GetBuffer(nBufferSize);
    ofn.nMaxFile = nBufferSize;
    // Set the current file directory as default folder
    CString curfile = m_wndPlaylistBar.GetCurFileName();
    CPathW defaultDir; // must outlive DoModal(), ofn.lpstrInitialDir points into it
    if (!PathUtils::IsURL(curfile)) {
        ExtendMaxPathLengthIfNeeded(curfile, true);
        defaultDir = curfile.GetString();
        defaultDir.RemoveFileSpec();
        if (!defaultDir.m_strPath.IsEmpty() && defaultDir.IsDirectory()) {
            ofn.lpstrInitialDir = defaultDir.m_strPath;
        }
    }

    if (fd.DoModal() == IDOK) {
        bool bFirstFile = true;
        CAtlList<CString> subfiles;
        FileDialogUtils::GetSelectedPaths(fd, subfiles);
        POSITION pos = subfiles.GetHeadPosition();
        while (pos) {
            const CString& subfile = subfiles.GetNext(pos);
            if (m_pDVS) {
                if (SUCCEEDED(m_pDVS->put_FileName((LPWSTR)(LPCWSTR)subfile))) {
                    m_pDVS->put_SelectedLanguage(0);
                    m_pDVS->put_HideSubtitles(true);
                    m_pDVS->put_HideSubtitles(false);
                    break;
                }
            } else {
                SubtitleInput subInput;
                if (LoadSubtitle(subfile, &subInput) && bFirstFile) {
                    bFirstFile = false;
                    // Use the subtitles file that was just added
                    AfxGetAppSettings().fEnableSubtitles = true;
                    SetSubtitle(subInput);
                }
            }
        }
    }
}

void CMainFrame::OnUpdateFileSubtitlesLoad(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(!m_fAudioOnly && (m_pCAP || m_pDVS) && GetLoadState() == MLS::LOADED && !IsPlaybackCaptureMode());
}

void CMainFrame::SubtitlesSave(const TCHAR* directory, bool silent)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }
    if (GetPlaybackMode() != PM_FILE && GetPlaybackMode() != PM_DVD) {
        return;
    }

    int i = 0;
    SubtitleInput* pSubInput = GetSubtitleInput(i, true);
    if (!pSubInput || !pSubInput->pSubStream) {
        return;
    }

    CLSID clsid;
    if (FAILED(pSubInput->pSubStream->GetClassID(&clsid))) {
        return;
    }

    bool format_rts    = (clsid == __uuidof(CRenderedTextSubtitle));
    bool format_vobsub = (clsid == __uuidof(CVobSubFile));
    if (!format_rts && !format_vobsub) {
        AfxMessageBox(_T("This operation is not supported.\r\nThe current subtitle can not be saved."), MB_ICONEXCLAMATION | MB_OK);
    }

    CString suggestedFileName;
    if (lastOpenFile.IsEmpty() || PathUtils::IsURL(lastOpenFile)) {
        if (silent) {
            return;
        }
        suggestedFileName = _T("subtitle");
    } else {
        CPath path(lastOpenFile);
        path.RemoveExtension();
        suggestedFileName = CString(path);
    }

    if (directory && *directory) {
        CPath suggestedPath(suggestedFileName);
        int pos = suggestedPath.FindFileName();
        CString fileName = suggestedPath.m_strPath.Mid(pos);
        CPath dirPath(directory);
        if (dirPath.IsRelative()) {
            dirPath = CPath(suggestedPath.m_strPath.Left(pos)) += dirPath;
        }
        if (EnsureDirectory(dirPath)) {
            suggestedFileName = CString(dirPath += fileName);
        }
        else if (silent) {
            return;
        }
    }

    CAppSettings& s = AfxGetAppSettings();
    bool isSaved = false;
    if (format_vobsub) {
        CVobSubFile* pVSF = (CVobSubFile*)(ISubStream*)pSubInput->pSubStream;

        // remember to set lpszDefExt to the first extension in the filter so that the save dialog autocompletes the extension
        // and tracks attempts to overwrite in a graceful manner
        if (silent) {
            isSaved = pVSF->Save(suggestedFileName + _T(".idx"), m_pCAP->GetSubtitleDelay());
        } else {
            CSaveSubtitlesFileDialog fd(m_pCAP->GetSubtitleDelay(), _T("idx"), suggestedFileName,
                _T("VobSub (*.idx, *.sub)|*.idx;*.sub||"), GetModalParent());

            if (fd.DoModal() == IDOK) {
                CAutoLock cAutoLock(&m_csSubLock);
                isSaved = pVSF->Save(fd.GetPathName(), fd.GetDelay());
            }
        }
    }
    else if (format_rts) {
        CRenderedTextSubtitle* pRTS = (CRenderedTextSubtitle*)(ISubStream*)pSubInput->pSubStream;

        if (s.bAddLangCodeWhenSaveSubtitles && pRTS->m_lcid && pRTS->m_lcid != LCID(-1)) {
            CString str;
            GetLocaleString(pRTS->m_lcid, LOCALE_SISO639LANGNAME, str);
            suggestedFileName += _T('.') + str;

            if (pRTS->m_eHearingImpaired == Subtitle::HI_YES) {
                suggestedFileName += _T(".hi");
            }
        }

        // same thing as in the case of CVobSubFile above for lpszDefExt
        if (silent) {
            Subtitle::SubType type;
            switch (pRTS->m_subtitleType)
            {
                case Subtitle::ASS:
                case Subtitle::SSA:
                case Subtitle::VTT:
                    type = Subtitle::ASS;
                    break;
                default:
                    type = Subtitle::SRT;
            }

            isSaved = pRTS->SaveAs(
                suggestedFileName, type, m_pCAP->GetFPS(), m_pCAP->GetSubtitleDelay(),
                pRTS->m_encoding, s.bSubSaveExternalStyleFile);
        } else {
            const std::vector<Subtitle::SubType> types = {
                Subtitle::SRT,
                Subtitle::SUB,
                Subtitle::SMI,
                Subtitle::PSB,
                Subtitle::SSA,
                Subtitle::ASS
            };

            CString filter;
            filter += _T("SubRip (*.srt)|*.srt|"); //1 = default
            filter += _T("MicroDVD (*.sub)|*.sub|"); //2
            filter += _T("SAMI (*.smi)|*.smi|"); //3
            filter += _T("PowerDivX (*.psb)|*.psb|"); //4
            filter += _T("SubStation Alpha (*.ssa)|*.ssa|"); //5
            filter += _T("Advanced SubStation Alpha (*.ass)|*.ass|"); //6
            filter += _T("|");

            CSaveSubtitlesFileDialog fd(pRTS->m_encoding, m_pCAP->GetSubtitleDelay(), s.bSubSaveExternalStyleFile,
                                        _T("srt"), suggestedFileName, filter, types, GetModalParent());

            if (pRTS->m_subtitleType == Subtitle::SSA || pRTS->m_subtitleType == Subtitle::ASS) {
                fd.m_ofn.nFilterIndex = 6; //nFilterIndex is 1-based
            }

            if (fd.DoModal() == IDOK) {
                CAutoLock cAutoLock(&m_csSubLock);
                s.bSubSaveExternalStyleFile = fd.GetSaveExternalStyleFile();
                isSaved = pRTS->SaveAs(fd.GetPathName(), types[fd.m_ofn.nFilterIndex - 1], m_pCAP->GetFPS(), fd.GetDelay(), fd.GetEncoding(), fd.GetSaveExternalStyleFile());
            }
        }
    }

    if (isSaved && s.fKeepHistory) {
        auto subPath = pSubInput->pSubStream->GetPath();
        if (!subPath.IsEmpty()) {
            s.MRU.AddSubToCurrent(subPath);
        }
    }
}

// Guards against copying typesetting rather than dialogue; generous enough for
// ordinary subtitles, which are a handful of lines at most.
static const int MAX_AUTOCOPY_SUBTITLE_LINES = 8;
static const int MAX_AUTOCOPY_SUBTITLE_LENGTH = 1000;
// No line of dialogue is on screen for less time than this, while animation and
// karaoke effects are built from events that are much shorter.
static const REFERENCE_TIME MIN_AUTOCOPY_SUBTITLE_DURATION = 250 * 10000i64;

static CStringW StripMarkupTags(CStringW str)
{
    int i = 0;
    while ((i = str.Find(L'<', i)) >= 0) {
        // only remove spans that look like markup tags, e.g. <i> or </font>
        WCHAR c = i + 1 < str.GetLength() ? str[i + 1] : L'\0';
        if (c != L'/' && !iswalpha(c)) {
            i++;
            continue;
        }
        int j = str.Find(L'>', i + 1);
        if (j < 0) {
            break;
        }
        str.Delete(i, j - i + 1);
    }
    return str;
}

// Copies the subtitle shown at rtNow to the clipboard and returns the time the
// caller should call again: the start of the next subtitle segment, since
// nothing can change before then.
REFERENCE_TIME CMainFrame::CopyCurrentSubtitleToClipboard(REFERENCE_TIME rtNow)
{
    const CAppSettings& s = AfxGetAppSettings();
    ASSERT(s.bAutoCopySubtitleToClipboard);
    if (!s.fEnableSubtitles || !m_pCAP) {
        return rtNow;
    }

    double fps = m_pCAP->GetFPS();
    if (fps <= 0.0) {
        fps = 25.0;
    }
    const REFERENCE_TIME rtDelay = (REFERENCE_TIME)m_pCAP->GetSubtitleDelay() * 10000; // ms -> reference time
    const REFERENCE_TIME rtSub = rtNow - rtDelay;

    CStringW strText;
    REFERENCE_TIME rtNext;
    {
        CAutoLock cAutoLock(&m_csSubLock);

        auto pRTS = dynamic_cast<CRenderedTextSubtitle*>((ISubStream*)m_pCurrentSubInput.pSubStream);
        if (!pRTS) {
            return rtNow;
        }

        int iSegment = -1, nSegments = 0;
        const STSSegment* pSeg = pRTS->SearchSubs(rtSub, fps, &iSegment, &nSegments);

        int iNext;
        if (pSeg) {
            iNext = iSegment + 1;
        } else {
            // between or before segments: find the first one starting after now
            int lo = 0, hi = nSegments;
            while (lo < hi) {
                int mid = (lo + hi) / 2;
                if (pRTS->TranslateSegmentStart(mid, fps) > rtSub) {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            iNext = lo;
        }
        if (iNext < nSegments) {
            rtNext = pRTS->TranslateSegmentStart(iNext, fps) + rtDelay;
        } else if (m_pCurrentSubInput.pSourceFilter) {
            rtNext = rtNow; // embedded subtitles: more can still be added while demuxing
        } else {
            rtNext = _I64_MAX;
        }

        if (!pSeg) {
            m_nLastCopiedSubSegment = -1;
            return rtNext;
        }
        if (iSegment == m_nLastCopiedSubSegment) {
            return rtNext;
        }
        m_nLastCopiedSubSegment = iSegment;

        // Typeset and karaoke effects can put hundreds of fragments on screen
        // at the same instant, often a single character each. That is artwork
        // rather than dialogue, and copying it only fills the clipboard with
        // noise. Judge the text that results rather than the number of events,
        // because a heavily typeset scene is mostly positioning and drawing
        // commands that carry no text at all.
        int nLines = 0;
        for (size_t i = 0; i < pSeg->subs.GetCount(); i++) {
            int subIndex = pSeg->subs[i];
            if (subIndex < 0 || subIndex >= (int)pRTS->GetCount()) {
                continue;
            }
            if (pRTS->TranslateEnd(subIndex, fps) - pRTS->TranslateStart(subIndex, fps) < MIN_AUTOCOPY_SUBTITLE_DURATION) {
                continue;
            }
            CStringW line = StripMarkupTags(pRTS->GetStrW(subIndex));
            line.Trim();
            if (line.IsEmpty()) {
                continue;
            }
            if (++nLines > MAX_AUTOCOPY_SUBTITLE_LINES
                    || strText.GetLength() + line.GetLength() > MAX_AUTOCOPY_SUBTITLE_LENGTH) {
                strText.Empty();
                break;
            }
            if (!strText.IsEmpty()) {
                strText += L'\n';
            }
            strText += line;
        }
    }

    // Clipboard access can block on other applications, keep it outside of m_csSubLock
    if (!strText.IsEmpty()) {
        strText.Replace(L"\n", L"\r\n");
        CClipboard clipboard(this);
        clipboard.SetText(CString(strText));
    }

    return rtNext;
}

void CMainFrame::OnUpdateFileSubtitlesSave(CCmdUI* pCmdUI)
{
    bool bEnable = false;

    if (!m_pCurrentSubInput.pSourceFilter) {
        if (auto pRTS = dynamic_cast<CRenderedTextSubtitle*>((ISubStream*)m_pCurrentSubInput.pSubStream)) {
            bEnable = !pRTS->IsEmpty();
        } else if (dynamic_cast<CVobSubFile*>((ISubStream*)m_pCurrentSubInput.pSubStream)) {
            bEnable = true;
        }
    }

    pCmdUI->Enable(bEnable);
}

#if 0
void CMainFrame::OnFileSubtitlesUpload()
{
    m_wndSubtitlesUploadDialog.ShowWindow(SW_SHOW);
}

void CMainFrame::OnUpdateFileSubtitlesUpload(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    pCmdUI->Enable(!m_pSubStreams.IsEmpty() && s.fEnableSubtitles);
}
#endif

void CMainFrame::OnFileSubtitlesDownload()
{
    if (!m_fAudioOnly) {
        if (m_pCAP && AfxGetAppSettings().IsISRAutoLoadEnabled()) {
            m_wndSubtitlesDownloadDialog.ShowWindow(SW_SHOW);
        } else {
            AfxMessageBox(_T("Downloading subtitles only works when using the internal subtitle renderer."), MB_ICONINFORMATION | MB_OK, 0);
        }
    }
}

void CMainFrame::OnUpdateFileSubtitlesDownload(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !IsPlaybackCaptureMode() && m_pCAP && !m_fAudioOnly);
}

void CMainFrame::OnFileProperties()
{
    CString fn;
    CString ydlsrc;
    if (m_pDVBState) {
        fn = m_pDVBState->sChannelName;
    } else {
        CPlaylistItem pli;
        if (m_wndPlaylistBar.GetCur(pli, true)) {
            fn = pli.m_fns.GetHead();
            if (pli.m_bYoutubeDL) {
                ydlsrc = pli.m_ydlSourceURL;
            }
        }
    }

    ASSERT(!fn.IsEmpty());

    CPPageFileInfoSheet fileinfo(fn, ydlsrc, this, GetModalParent());
    fileinfo.DoModal();
}

void CMainFrame::OnUpdateFileProperties(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && GetPlaybackMode() != PM_ANALOG_CAPTURE);
}

void CMainFrame::OnFileOpenLocation() {
    CString filePath = m_wndPlaylistBar.GetCurFileName();
    if (!PathUtils::IsURL(filePath)) {
        ExploreToFile(filePath);
    }
}

void CMainFrame::OnFileCloseMedia()
{
    if (USE_LOGGER(AfxGetAppSettings())) {
        PLAYER_LOG(_T("CMainFrame::OnFileCloseMedia"));
    }

    CloseMedia();
}

void CMainFrame::OnUpdateViewTearingTest(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    bool supported = (s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                      || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                      || s.iDSVideoRendererType == VIDRNDT_DS_SYNC);

    pCmdUI->Enable(supported && GetLoadState() == MLS::LOADED && !m_fAudioOnly);
    pCmdUI->SetCheck(supported && AfxGetMyApp()->m_Renderers.m_bTearingTest);
}

void CMainFrame::OnViewTearingTest()
{
    AfxGetMyApp()->m_Renderers.m_bTearingTest = !AfxGetMyApp()->m_Renderers.m_bTearingTest;
}

void CMainFrame::OnUpdateViewDisplayRendererStats(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    bool supported = (s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                      || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                      || s.iDSVideoRendererType == VIDRNDT_DS_SYNC
                      || s.iDSVideoRendererType == VIDRNDT_DS_MPCVR);

    pCmdUI->Enable(supported && GetLoadState() == MLS::LOADED && !m_fAudioOnly);
    pCmdUI->SetCheck(supported && AfxGetMyApp()->m_Renderers.m_iDisplayStats > 0);
}

void CMainFrame::OnViewResetRendererStats()
{
    AfxGetMyApp()->m_Renderers.m_bResetStats = true; // Reset by "consumer"
}

void CMainFrame::OnViewDisplayRendererStats()
{
    const CAppSettings& s = AfxGetAppSettings();
    bool supported = (s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                      || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                      || s.iDSVideoRendererType == VIDRNDT_DS_SYNC
                      || s.iDSVideoRendererType == VIDRNDT_DS_MPCVR);

    if (supported) {
        if (m_pCAP3) {
            m_pCAP3->ToggleStats();
            return;
        }

        if (!AfxGetMyApp()->m_Renderers.m_iDisplayStats) {
            AfxGetMyApp()->m_Renderers.m_bResetStats = true; // to reset statistics on first call ...
        }

        ++AfxGetMyApp()->m_Renderers.m_iDisplayStats;
        if (AfxGetMyApp()->m_Renderers.m_iDisplayStats > 3) {
            AfxGetMyApp()->m_Renderers.m_iDisplayStats = 0;
        }
        RepaintVideo();
    }
}

void CMainFrame::OnUpdateViewVSync(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(!supported || r.m_AdvRendSets.bVMR9VSync);
}

void CMainFrame::OnUpdateViewVSyncOffset(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D
                      && r.m_AdvRendSets.bVMR9AlterativeVSync);

    pCmdUI->Enable(supported);
    CString Temp;
    Temp.Format(L"%d", r.m_AdvRendSets.iVMR9VSyncOffset);
    pCmdUI->SetText(Temp);
    CMPCThemeMenu::updateItem(pCmdUI);
}

void CMainFrame::OnUpdateViewVSyncAccurate(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9VSyncAccurate);
}

void CMainFrame::OnUpdateViewSynchronizeVideo(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_SYNC) && GetPlaybackMode() == PM_NONE);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bSynchronizeVideo);
}

void CMainFrame::OnUpdateViewSynchronizeDisplay(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_SYNC) && GetPlaybackMode() == PM_NONE);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bSynchronizeDisplay);
}

void CMainFrame::OnUpdateViewSynchronizeNearest(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = (s.iDSVideoRendererType == VIDRNDT_DS_SYNC);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bSynchronizeNearest);
}

void CMainFrame::OnUpdateViewColorManagementEnable(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP16Support;

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9ColorManagementEnable);
}

void CMainFrame::OnUpdateViewColorManagementInput(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP16Support
                     && r.m_AdvRendSets.bVMR9ColorManagementEnable;

    pCmdUI->Enable(supported);

    switch (pCmdUI->m_nID) {
        case ID_VIEW_CM_INPUT_AUTO:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementInput == VIDEO_SYSTEM_UNKNOWN);
            break;

        case ID_VIEW_CM_INPUT_HDTV:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementInput == VIDEO_SYSTEM_HDTV);
            break;

        case ID_VIEW_CM_INPUT_SDTV_NTSC:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementInput == VIDEO_SYSTEM_SDTV_NTSC);
            break;

        case ID_VIEW_CM_INPUT_SDTV_PAL:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementInput == VIDEO_SYSTEM_SDTV_PAL);
            break;
    }
}

void CMainFrame::OnUpdateViewColorManagementAmbientLight(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP16Support &&
                     r.m_AdvRendSets.bVMR9ColorManagementEnable;

    pCmdUI->Enable(supported);

    switch (pCmdUI->m_nID) {
        case ID_VIEW_CM_AMBIENTLIGHT_BRIGHT:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementAmbientLight == AMBIENT_LIGHT_BRIGHT);
            break;
        case ID_VIEW_CM_AMBIENTLIGHT_DIM:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementAmbientLight == AMBIENT_LIGHT_DIM);
            break;
        case ID_VIEW_CM_AMBIENTLIGHT_DARK:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementAmbientLight == AMBIENT_LIGHT_DARK);
            break;
    }
}

void CMainFrame::OnUpdateViewColorManagementIntent(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP16Support
                     && r.m_AdvRendSets.bVMR9ColorManagementEnable;

    pCmdUI->Enable(supported);

    switch (pCmdUI->m_nID) {
        case ID_VIEW_CM_INTENT_PERCEPTUAL:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementIntent == COLOR_RENDERING_INTENT_PERCEPTUAL);
            break;
        case ID_VIEW_CM_INTENT_RELATIVECOLORIMETRIC:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementIntent == COLOR_RENDERING_INTENT_RELATIVE_COLORIMETRIC);
            break;
        case ID_VIEW_CM_INTENT_SATURATION:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementIntent == COLOR_RENDERING_INTENT_SATURATION);
            break;
        case ID_VIEW_CM_INTENT_ABSOLUTECOLORIMETRIC:
            pCmdUI->SetCheck(r.m_AdvRendSets.iVMR9ColorManagementIntent == COLOR_RENDERING_INTENT_ABSOLUTE_COLORIMETRIC);
            break;
    }
}

void CMainFrame::OnUpdateViewEVROutputRange(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                       || s.iDSVideoRendererType == VIDRNDT_DS_SYNC)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);

    if (pCmdUI->m_nID == ID_VIEW_EVROUTPUTRANGE_0_255) {
        pCmdUI->SetCheck(r.m_AdvRendSets.iEVROutputRange == 0);
    } else if (pCmdUI->m_nID == ID_VIEW_EVROUTPUTRANGE_16_235) {
        pCmdUI->SetCheck(r.m_AdvRendSets.iEVROutputRange == 1);
    }
}

void CMainFrame::OnUpdateViewFlushGPU(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);

    if (pCmdUI->m_nID == ID_VIEW_FLUSHGPU_BEFOREVSYNC) {
        pCmdUI->SetCheck(r.m_AdvRendSets.bVMRFlushGPUBeforeVSync);
    } else if (pCmdUI->m_nID == ID_VIEW_FLUSHGPU_AFTERPRESENT) {
        pCmdUI->SetCheck(r.m_AdvRendSets.bVMRFlushGPUAfterPresent);
    } else if (pCmdUI->m_nID == ID_VIEW_FLUSHGPU_WAIT) {
        pCmdUI->SetCheck(r.m_AdvRendSets.bVMRFlushGPUWait);
    }

}

void CMainFrame::OnUpdateViewD3DFullscreen(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                       || s.iDSVideoRendererType == VIDRNDT_DS_SYNC)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(s.fD3DFullscreen);
}

void CMainFrame::OnUpdateViewDisableDesktopComposition(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                       || s.iDSVideoRendererType == VIDRNDT_DS_SYNC)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D
                      && !IsWindows8OrGreater());

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(supported && r.m_AdvRendSets.bVMRDisableDesktopComposition);
}

void CMainFrame::OnUpdateViewAlternativeVSync(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9AlterativeVSync);
}

void CMainFrame::OnUpdateViewFullscreenGUISupport(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9FullscreenGUISupport);
}

void CMainFrame::OnUpdateViewHighColorResolution(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM
                       || s.iDSVideoRendererType == VIDRNDT_DS_SYNC)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_b10bitSupport;

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bEVRHighColorResolution);
}

void CMainFrame::OnUpdateViewForceInputHighColorResolution(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_b10bitSupport;

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bEVRForceInputHighColorResolution);
}

void CMainFrame::OnUpdateViewFullFloatingPointProcessing(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP32Support;

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9FullFloatingPointProcessing);
}

void CMainFrame::OnUpdateViewHalfFloatingPointProcessing(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    const CRenderersData& rd = AfxGetMyApp()->m_Renderers;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                       || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                     && rd.m_bFP16Support;

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing);
}

void CMainFrame::OnUpdateViewEnableFrameTimeCorrection(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = ((s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                      && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D);

    pCmdUI->Enable(supported);
    pCmdUI->SetCheck(r.m_AdvRendSets.bEVREnableFrameTimeCorrection);
}

void CMainFrame::OnUpdateViewVSyncOffsetIncrease(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = s.iDSVideoRendererType == VIDRNDT_DS_SYNC
                     || (((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                           || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                          && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                         && r.m_AdvRendSets.bVMR9AlterativeVSync);

    pCmdUI->Enable(supported);
}

void CMainFrame::OnUpdateViewVSyncOffsetDecrease(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    const CRenderersSettings& r = s.m_RenderersSettings;
    bool supported = s.iDSVideoRendererType == VIDRNDT_DS_SYNC
                     || (((s.iDSVideoRendererType == VIDRNDT_DS_VMR9RENDERLESS
                           || s.iDSVideoRendererType == VIDRNDT_DS_EVR_CUSTOM)
                          && r.iAPSurfaceUsage == VIDRNDT_AP_TEXTURE3D)
                         && r.m_AdvRendSets.bVMR9AlterativeVSync);

    pCmdUI->Enable(supported);
}

void CMainFrame::OnViewVSync()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9VSync = !r.m_AdvRendSets.bVMR9VSync;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9VSync
                                              ? IDS_OSD_RS_VSYNC_ON : IDS_OSD_RS_VSYNC_OFF));
}

void CMainFrame::OnViewVSyncAccurate()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9VSyncAccurate = !r.m_AdvRendSets.bVMR9VSyncAccurate;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9VSyncAccurate
                                              ? IDS_OSD_RS_ACCURATE_VSYNC_ON : IDS_OSD_RS_ACCURATE_VSYNC_OFF));
}

void CMainFrame::OnViewSynchronizeVideo()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bSynchronizeVideo = !r.m_AdvRendSets.bSynchronizeVideo;
    if (r.m_AdvRendSets.bSynchronizeVideo) {
        r.m_AdvRendSets.bSynchronizeDisplay = false;
        r.m_AdvRendSets.bSynchronizeNearest = false;
        r.m_AdvRendSets.bVMR9VSync = false;
        r.m_AdvRendSets.bVMR9VSyncAccurate = false;
        r.m_AdvRendSets.bVMR9AlterativeVSync = false;
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bSynchronizeVideo
                                              ? IDS_OSD_RS_SYNC_TO_DISPLAY_ON : IDS_OSD_RS_SYNC_TO_DISPLAY_ON));
}

void CMainFrame::OnViewSynchronizeDisplay()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bSynchronizeDisplay = !r.m_AdvRendSets.bSynchronizeDisplay;
    if (r.m_AdvRendSets.bSynchronizeDisplay) {
        r.m_AdvRendSets.bSynchronizeVideo = false;
        r.m_AdvRendSets.bSynchronizeNearest = false;
        r.m_AdvRendSets.bVMR9VSync = false;
        r.m_AdvRendSets.bVMR9VSyncAccurate = false;
        r.m_AdvRendSets.bVMR9AlterativeVSync = false;
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bSynchronizeDisplay
                                              ? IDS_OSD_RS_SYNC_TO_VIDEO_ON : IDS_OSD_RS_SYNC_TO_VIDEO_ON));
}

void CMainFrame::OnViewSynchronizeNearest()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bSynchronizeNearest = !r.m_AdvRendSets.bSynchronizeNearest;
    if (r.m_AdvRendSets.bSynchronizeNearest) {
        r.m_AdvRendSets.bSynchronizeVideo = false;
        r.m_AdvRendSets.bSynchronizeDisplay = false;
        r.m_AdvRendSets.bVMR9VSync = false;
        r.m_AdvRendSets.bVMR9VSyncAccurate = false;
        r.m_AdvRendSets.bVMR9AlterativeVSync = false;
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bSynchronizeNearest
                                              ? IDS_OSD_RS_PRESENT_NEAREST_ON : IDS_OSD_RS_PRESENT_NEAREST_OFF));
}

void CMainFrame::OnViewColorManagementEnable()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9ColorManagementEnable = !r.m_AdvRendSets.bVMR9ColorManagementEnable;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9ColorManagementEnable
                                              ? IDS_OSD_RS_COLOR_MANAGEMENT_ON : IDS_OSD_RS_COLOR_MANAGEMENT_OFF));
}

void CMainFrame::OnViewColorManagementInputAuto()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementInput = VIDEO_SYSTEM_UNKNOWN;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_INPUT_TYPE_AUTO));
}

void CMainFrame::OnViewColorManagementInputHDTV()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementInput = VIDEO_SYSTEM_HDTV;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_INPUT_TYPE_HDTV));
}

void CMainFrame::OnViewColorManagementInputSDTV_NTSC()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementInput = VIDEO_SYSTEM_SDTV_NTSC;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_INPUT_TYPE_SD_NTSC));
}

void CMainFrame::OnViewColorManagementInputSDTV_PAL()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementInput = VIDEO_SYSTEM_SDTV_PAL;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_INPUT_TYPE_SD_PAL));
}

void CMainFrame::OnViewColorManagementAmbientLightBright()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementAmbientLight = AMBIENT_LIGHT_BRIGHT;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_AMBIENT_LIGHT_BRIGHT));
}

void CMainFrame::OnViewColorManagementAmbientLightDim()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementAmbientLight = AMBIENT_LIGHT_DIM;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_AMBIENT_LIGHT_DIM));
}

void CMainFrame::OnViewColorManagementAmbientLightDark()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementAmbientLight = AMBIENT_LIGHT_DARK;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_AMBIENT_LIGHT_DARK));
}

void CMainFrame::OnViewColorManagementIntentPerceptual()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementIntent = COLOR_RENDERING_INTENT_PERCEPTUAL;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_REND_INTENT_PERCEPT));
}

void CMainFrame::OnViewColorManagementIntentRelativeColorimetric()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementIntent = COLOR_RENDERING_INTENT_RELATIVE_COLORIMETRIC;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_REND_INTENT_RELATIVE));
}

void CMainFrame::OnViewColorManagementIntentSaturation()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementIntent = COLOR_RENDERING_INTENT_SATURATION;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_REND_INTENT_SATUR));
}

void CMainFrame::OnViewColorManagementIntentAbsoluteColorimetric()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iVMR9ColorManagementIntent = COLOR_RENDERING_INTENT_ABSOLUTE_COLORIMETRIC;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_REND_INTENT_ABSOLUTE));
}

void CMainFrame::OnViewEVROutputRange_0_255()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iEVROutputRange = 0;
    CString strOSD;
    strOSD.Format(IDS_OSD_RS_OUTPUT_RANGE, _T("0 - 255"));
    m_OSD.DisplayMessage(OSD_TOPRIGHT, strOSD);
}

void CMainFrame::OnViewEVROutputRange_16_235()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.iEVROutputRange = 1;
    CString strOSD;
    strOSD.Format(IDS_OSD_RS_OUTPUT_RANGE, _T("16 - 235"));
    m_OSD.DisplayMessage(OSD_TOPRIGHT, strOSD);
}

void CMainFrame::OnViewFlushGPUBeforeVSync()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMRFlushGPUBeforeVSync = !r.m_AdvRendSets.bVMRFlushGPUBeforeVSync;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMRFlushGPUBeforeVSync
                                              ? IDS_OSD_RS_FLUSH_BEF_VSYNC_ON : IDS_OSD_RS_FLUSH_BEF_VSYNC_OFF));
}

void CMainFrame::OnViewFlushGPUAfterVSync()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMRFlushGPUAfterPresent = !r.m_AdvRendSets.bVMRFlushGPUAfterPresent;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMRFlushGPUAfterPresent
                                              ? IDS_OSD_RS_FLUSH_AFT_PRES_ON : IDS_OSD_RS_FLUSH_AFT_PRES_OFF));
}

void CMainFrame::OnViewFlushGPUWait()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMRFlushGPUWait = !r.m_AdvRendSets.bVMRFlushGPUWait;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMRFlushGPUWait
                                              ? IDS_OSD_RS_WAIT_ON : IDS_OSD_RS_WAIT_OFF));
}

void CMainFrame::OnViewD3DFullScreen()
{
    CAppSettings& r = AfxGetAppSettings();
    r.fD3DFullscreen = !r.fD3DFullscreen;
    r.SaveSettings();
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.fD3DFullscreen
                                              ? IDS_OSD_RS_D3D_FULLSCREEN_ON : IDS_OSD_RS_D3D_FULLSCREEN_OFF));
}

void CMainFrame::OnViewDisableDesktopComposition()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMRDisableDesktopComposition = !r.m_AdvRendSets.bVMRDisableDesktopComposition;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMRDisableDesktopComposition
                                              ? IDS_OSD_RS_NO_DESKTOP_COMP_ON : IDS_OSD_RS_NO_DESKTOP_COMP_OFF));
}

void CMainFrame::OnViewAlternativeVSync()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9AlterativeVSync = !r.m_AdvRendSets.bVMR9AlterativeVSync;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9AlterativeVSync
                                              ? IDS_OSD_RS_ALT_VSYNC_ON : IDS_OSD_RS_ALT_VSYNC_OFF));
}

void CMainFrame::OnViewResetDefault()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.SetDefault();
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_OSD_RS_RESET_DEFAULT));
}

void CMainFrame::OnViewFullscreenGUISupport()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9FullscreenGUISupport = !r.m_AdvRendSets.bVMR9FullscreenGUISupport;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9FullscreenGUISupport
                                              ? IDS_OSD_RS_D3D_FS_GUI_SUPP_ON : IDS_OSD_RS_D3D_FS_GUI_SUPP_OFF));
}

void CMainFrame::OnViewHighColorResolution()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bEVRHighColorResolution = !r.m_AdvRendSets.bEVRHighColorResolution;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bEVRHighColorResolution
                                              ? IDS_OSD_RS_10BIT_RBG_OUT_ON : IDS_OSD_RS_10BIT_RBG_OUT_OFF));
}

void CMainFrame::OnViewForceInputHighColorResolution()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bEVRForceInputHighColorResolution = !r.m_AdvRendSets.bEVRForceInputHighColorResolution;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bEVRForceInputHighColorResolution
                                              ? IDS_OSD_RS_10BIT_RBG_IN_ON : IDS_OSD_RS_10BIT_RBG_IN_OFF));
}

void CMainFrame::OnViewFullFloatingPointProcessing()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    if (!r.m_AdvRendSets.bVMR9FullFloatingPointProcessing) {
        if (AfxMessageBox(_T("WARNING: Full Floating Point processing can sometimes cause problems. With some videos it can cause the player to freeze, crash, or display corrupted video. This happens mostly with Intel GPUs.\n\nAre you really sure that you want to enable this setting?"), MB_YESNO) == IDNO) {
            return;
        }
    }
    r.m_AdvRendSets.bVMR9FullFloatingPointProcessing = !r.m_AdvRendSets.bVMR9FullFloatingPointProcessing;
    if (r.m_AdvRendSets.bVMR9FullFloatingPointProcessing) {
        r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing = false;
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9FullFloatingPointProcessing
                                              ? IDS_OSD_RS_FULL_FP_PROCESS_ON : IDS_OSD_RS_FULL_FP_PROCESS_OFF));
}

void CMainFrame::OnViewHalfFloatingPointProcessing()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing = !r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing;
    if (r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing) {
        r.m_AdvRendSets.bVMR9FullFloatingPointProcessing = false;
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bVMR9HalfFloatingPointProcessing
                                              ? IDS_OSD_RS_HALF_FP_PROCESS_ON : IDS_OSD_RS_HALF_FP_PROCESS_OFF));
}

void CMainFrame::OnViewEnableFrameTimeCorrection()
{
    CRenderersSettings& r = AfxGetAppSettings().m_RenderersSettings;
    r.m_AdvRendSets.bEVREnableFrameTimeCorrection = !r.m_AdvRendSets.bEVREnableFrameTimeCorrection;
    m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(r.m_AdvRendSets.bEVREnableFrameTimeCorrection
                                              ? IDS_OSD_RS_FT_CORRECTION_ON : IDS_OSD_RS_FT_CORRECTION_OFF));
}

void CMainFrame::OnViewVSyncOffsetIncrease()
{
    CAppSettings& s = AfxGetAppSettings();
    CRenderersSettings& r = s.m_RenderersSettings;
    CString strOSD;
    if (s.iDSVideoRendererType == VIDRNDT_DS_SYNC) {
        r.m_AdvRendSets.fTargetSyncOffset = r.m_AdvRendSets.fTargetSyncOffset - 0.5; // Yeah, it should be a "-"
        strOSD.Format(IDS_OSD_RS_TARGET_VSYNC_OFFSET, r.m_AdvRendSets.fTargetSyncOffset);
    } else {
        ++r.m_AdvRendSets.iVMR9VSyncOffset;
        strOSD.Format(IDS_OSD_RS_VSYNC_OFFSET, r.m_AdvRendSets.iVMR9VSyncOffset);
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, strOSD);
}

void CMainFrame::OnViewVSyncOffsetDecrease()
{
    CAppSettings& s = AfxGetAppSettings();
    CRenderersSettings& r = s.m_RenderersSettings;
    CString strOSD;
    if (s.iDSVideoRendererType == VIDRNDT_DS_SYNC) {
        r.m_AdvRendSets.fTargetSyncOffset = r.m_AdvRendSets.fTargetSyncOffset + 0.5;
        strOSD.Format(IDS_OSD_RS_TARGET_VSYNC_OFFSET, r.m_AdvRendSets.fTargetSyncOffset);
    } else {
        --r.m_AdvRendSets.iVMR9VSyncOffset;
        strOSD.Format(IDS_OSD_RS_VSYNC_OFFSET, r.m_AdvRendSets.iVMR9VSyncOffset);
    }
    m_OSD.DisplayMessage(OSD_TOPRIGHT, strOSD);
}

void CMainFrame::OnUpdateViewOSDDisplayTime(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    pCmdUI->Enable(s.fShowOSD && GetLoadState() != MLS::CLOSED);
    pCmdUI->SetCheck(AfxGetAppSettings().fShowCurrentTimeInOSD);
}

void CMainFrame::OnViewOSDDisplayTime()
{
    auto &showTime = AfxGetAppSettings().fShowCurrentTimeInOSD;
    showTime = !showTime;

    if (!showTime) {
        m_OSD.ClearTime();
    }

    OnTimer(TIMER_STREAMPOSPOLLER2);
}

void CMainFrame::OnUpdateViewOSDShowFileName(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();
    pCmdUI->Enable(s.fShowOSD && GetLoadState() != MLS::CLOSED);
}

void CMainFrame::OnViewOSDShowFileName()
{
    CString strOSD;
    switch (GetPlaybackMode()) {
        case PM_FILE:
            strOSD = GetFileName();
            break;
        case PM_DVD:
            strOSD = _T("DVD");
            if (m_pDVDI) {
                CString path;
                ULONG len = 0;
                if (SUCCEEDED(m_pDVDI->GetDVDDirectory(path.GetBuffer(MAX_PATH), MAX_PATH, &len)) && len) {
                    path.ReleaseBuffer();
                    if (path.Find(_T("\\VIDEO_TS")) == 2) {
                        strOSD.AppendFormat(_T(" - %s"), GetDriveLabel(CPath(path)).GetString());
                    } else {
                        strOSD.AppendFormat(_T(" - %s"), path.GetString());
                    }
                }
            }
            break;
        case PM_ANALOG_CAPTURE:
            strOSD = GetCaptureTitle();
            break;
        case PM_DIGITAL_CAPTURE:
            UpdateCurrentChannelInfo(true, false);
            break;
        default: // Shouldn't happen
            ASSERT(FALSE);
            return;
    }
    if (!strOSD.IsEmpty()) {
        m_OSD.DisplayMessage(OSD_TOPLEFT, strOSD);
    }
}

void CMainFrame::OnUpdateShaderToggle1(CCmdUI* pCmdUI)
{
	if (AfxGetAppSettings().m_Shaders.GetCurrentPreset().GetPreResize().empty()) {
		pCmdUI->Enable(FALSE);
		pCmdUI->SetCheck (0);
	} else {
		pCmdUI->Enable(TRUE);
		pCmdUI->SetCheck (m_bToggleShader);
	}
}

void CMainFrame::OnUpdateShaderToggle2(CCmdUI* pCmdUI)
{
	CAppSettings& s = AfxGetAppSettings();

	if (s.m_Shaders.GetCurrentPreset().GetPostResize().empty()) {
		pCmdUI->Enable(FALSE);
		pCmdUI->SetCheck(0);
	} else {
		pCmdUI->Enable(TRUE);
		pCmdUI->SetCheck(m_bToggleShaderScreenSpace);
	}
}

void CMainFrame::OnShaderToggle1()
{
	m_bToggleShader = !m_bToggleShader;
    SetShaders(m_bToggleShader, m_bToggleShaderScreenSpace);
    if (m_bToggleShader) {
		m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_PRESIZE_SHADERS_ENABLED));
	} else {
		m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_PRESIZE_SHADERS_DISABLED));
	}

	if (m_pCAP) {
		RepaintVideo();
	}
}

void CMainFrame::OnShaderToggle2()
{
	m_bToggleShaderScreenSpace = !m_bToggleShaderScreenSpace;
    SetShaders(m_bToggleShader, m_bToggleShaderScreenSpace);
    if (m_bToggleShaderScreenSpace) {
        m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_POSTSIZE_SHADERS_ENABLED));
	} else {
        m_OSD.DisplayMessage(OSD_TOPRIGHT, ResStr(IDS_POSTSIZE_SHADERS_DISABLED));
	}

	if (m_pCAP) {
		RepaintVideo();
	}
}

void CMainFrame::OnD3DFullscreenToggle()
{
    CAppSettings& s = AfxGetAppSettings();
    CString strMsg;

    s.fD3DFullscreen = !s.fD3DFullscreen;
    strMsg.LoadString(s.fD3DFullscreen ? IDS_OSD_RS_D3D_FULLSCREEN_ON : IDS_OSD_RS_D3D_FULLSCREEN_OFF);
    if (GetLoadState() == MLS::CLOSED) {
        m_closingmsg = strMsg;
    } else {
        m_OSD.DisplayMessage(OSD_TOPRIGHT, strMsg);
    }
}

void CMainFrame::OnFileCloseAndRestore()
{
    if (GetLoadState() == MLS::LOADED && IsFullScreenMode()) {
        // exit fullscreen
        OnViewFullscreen();
    }
    SendMessage(WM_COMMAND, ID_FILE_CLOSEMEDIA);
    RestoreDefaultWindowRect();
}

void CMainFrame::OnUpdateFileClose(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED || GetLoadState() == MLS::LOADING);
}

// view

void CMainFrame::SetCaptionState(MpcCaptionState eState)
{
    auto& s = AfxGetAppSettings();

    if (eState == s.eCaptionMenuMode) {
        return;
    }

    const auto eOldState = s.eCaptionMenuMode;
    s.eCaptionMenuMode = eState;

    if (IsFullScreenMainFrame()) {
        return;
    }

    DWORD dwRemove = 0, dwAdd = 0;
    DWORD dwMenuFlags = GetMenuBarVisibility();

    CRect windowRect;

    const bool bZoomed = !!IsZoomed();

    if (!bZoomed) {
        GetWindowRect(&windowRect);
        CRect decorationsRect;
        VERIFY(AdjustWindowRectEx(decorationsRect, GetWindowStyle(m_hWnd), dwMenuFlags == AFX_MBV_KEEPVISIBLE, GetWindowExStyle(m_hWnd)));
        windowRect.bottom -= decorationsRect.bottom;
        windowRect.right  -= decorationsRect.right;
        windowRect.top    -= decorationsRect.top;
        windowRect.left   -= decorationsRect.left;
    }

    const int base = MpcCaptionState::MODE_COUNT;
    for (int i = eOldState; i != eState; i = (i + 1) % base) {
        switch (static_cast<MpcCaptionState>(i)) {
            case MpcCaptionState::MODE_BORDERLESS:
                dwMenuFlags = AFX_MBV_KEEPVISIBLE;
                dwAdd |= (WS_CAPTION | WS_THICKFRAME);
                dwRemove &= ~(WS_CAPTION | WS_THICKFRAME);
                break;
            case MpcCaptionState::MODE_SHOWCAPTIONMENU:
                dwMenuFlags = AFX_MBV_DISPLAYONFOCUS;
                break;
            case MpcCaptionState::MODE_HIDEMENU:
                dwMenuFlags = AFX_MBV_DISPLAYONFOCUS;
                dwAdd &= ~WS_CAPTION;
                dwRemove |= WS_CAPTION;
                break;
            case MpcCaptionState::MODE_FRAMEONLY:
                dwMenuFlags = AFX_MBV_DISPLAYONFOCUS;
                dwAdd &= ~WS_THICKFRAME;
                dwRemove |= WS_THICKFRAME;
                break;
            default:
                ASSERT(FALSE);
        }
    }

    UINT uFlags = SWP_NOZORDER;
    if (dwRemove != dwAdd) {
        uFlags |= SWP_FRAMECHANGED;
        VERIFY(SetWindowLong(m_hWnd, GWL_STYLE, (GetWindowLong(m_hWnd, GWL_STYLE) | dwAdd) & ~dwRemove));
    }

    SetMenuBarVisibility(dwMenuFlags);
    if (bZoomed) {
        CMonitors::GetNearestMonitor(this).GetWorkAreaRect(windowRect);
    } else {
        VERIFY(AdjustWindowRectEx(windowRect, GetWindowStyle(m_hWnd), dwMenuFlags == AFX_MBV_KEEPVISIBLE, GetWindowExStyle(m_hWnd)));
    }

    VERIFY(SetWindowPos(nullptr, windowRect.left, windowRect.top, windowRect.Width(), windowRect.Height(), uFlags));
    OSDBarSetPos();
}

void CMainFrame::OnViewCaptionmenu()
{
    const auto& s = AfxGetAppSettings();
    SetCaptionState(static_cast<MpcCaptionState>((s.eCaptionMenuMode + 1) % MpcCaptionState::MODE_COUNT));
}

void CMainFrame::OnUpdateViewCaptionmenu(CCmdUI* pCmdUI)
{
    const auto& s = AfxGetAppSettings();
    const UINT next[] = { IDS_VIEW_HIDEMENU, IDS_VIEW_FRAMEONLY, IDS_VIEW_BORDERLESS, IDS_VIEW_CAPTIONMENU };
    pCmdUI->SetText(ResStr(next[s.eCaptionMenuMode % MpcCaptionState::MODE_COUNT]));
    CMPCThemeMenu::updateItem(pCmdUI);
}

void CMainFrame::OnViewControlBar(UINT nID)
{
    nID -= ID_VIEW_SEEKER;
    m_controls.ToggleControl(static_cast<CMainFrameControls::Toolbar>(nID));
}

void CMainFrame::OnUpdateViewControlBar(CCmdUI* pCmdUI)
{
    const UINT nID = pCmdUI->m_nID - ID_VIEW_SEEKER;
    pCmdUI->SetCheck(m_controls.ControlChecked(static_cast<CMainFrameControls::Toolbar>(nID)));
    if (pCmdUI->m_nID == ID_VIEW_SEEKER) {
        pCmdUI->Enable(!IsPlaybackCaptureMode());
    }
}

void CMainFrame::OnViewSubresync()
{
    m_controls.ToggleControl(CMainFrameControls::Panel::SUBRESYNC);
    AdjustStreamPosPoller(true);
}

void CMainFrame::OnUpdateViewSubresync(CCmdUI* pCmdUI)
{
    pCmdUI->SetCheck(m_controls.ControlChecked(CMainFrameControls::Panel::SUBRESYNC));
    bool enabled = m_pCAP && m_pCurrentSubInput.pSubStream && !IsPlaybackCaptureMode();
    if (enabled) {
        CLSID clsid;
        m_pCurrentSubInput.pSubStream->GetClassID(&clsid);
        if (clsid == __uuidof(CRenderedTextSubtitle)) {
#if USE_LIBASS
            CRenderedTextSubtitle* pRTS = (CRenderedTextSubtitle*)(ISubStream*)m_pCurrentSubInput.pSubStream;
            enabled = !pRTS->m_LibassContext.IsLibassActive();
#endif
        } else {
            enabled = false;
        }
    }
    pCmdUI->Enable(enabled);
}

void CMainFrame::UpdatePlaylistButton() {
    m_wndToolBar.SetPlaylist(m_controls.ControlChecked(CMainFrameControls::Panel::PLAYLIST));
}

void CMainFrame::OnViewPlaylist()
{
    m_controls.ToggleControl(CMainFrameControls::Panel::PLAYLIST);
    m_wndPlaylistBar.SetHiddenDueToFullscreen(false);
    UpdatePlaylistButton();
    if (m_controls.ControlChecked(CMainFrameControls::Panel::PLAYLIST)) {
        m_wndPlaylistBar.EnsureCurrentVisible();
    }
}

void CMainFrame::OnUpdateViewPlaylist(CCmdUI* pCmdUI)
{
    pCmdUI->SetCheck(m_controls.ControlChecked(CMainFrameControls::Panel::PLAYLIST));
}

void CMainFrame::OnPlaylistToggleShuffle() {
    CAppSettings& s = AfxGetAppSettings();
    s.bShufflePlaylistItems = !s.bShufflePlaylistItems;
    m_wndPlaylistBar.m_pl.SetShuffle(s.bShufflePlaylistItems);
    m_wndToolBar.SetShuffle(s.bShufflePlaylistItems);
    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(s.bShufflePlaylistItems ? IDS_SHUFFLE_ON : IDS_SHUFFLE_OFF));
    m_media_trans_control.SetShuffleEnabled(s.bShufflePlaylistItems);
}

void CMainFrame::OnViewEditListEditor()
{
    CAppSettings& s = AfxGetAppSettings();

    if (s.fEnableEDLEditor || (AfxMessageBox(IDS_MB_SHOW_EDL_EDITOR, MB_ICONQUESTION | MB_YESNO, 0) == IDYES)) {
        s.fEnableEDLEditor = true;
        m_controls.ToggleControl(CMainFrameControls::Panel::EDL);
    }
}

void CMainFrame::OnEDLIn()
{
    if (AfxGetAppSettings().fEnableEDLEditor && (GetLoadState() == MLS::LOADED) && (GetPlaybackMode() == PM_FILE)) {
        REFERENCE_TIME rt;

        m_pMS->GetCurrentPosition(&rt);
        m_wndEditListEditor.SetIn(rt);
    }
}

void CMainFrame::OnUpdateEDLIn(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(m_controls.ControlChecked(CMainFrameControls::Panel::EDL));
}

void CMainFrame::OnEDLOut()
{
    if (AfxGetAppSettings().fEnableEDLEditor && (GetLoadState() == MLS::LOADED) && (GetPlaybackMode() == PM_FILE)) {
        REFERENCE_TIME rt;

        m_pMS->GetCurrentPosition(&rt);
        m_wndEditListEditor.SetOut(rt);
    }
}

void CMainFrame::OnUpdateEDLOut(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(m_controls.ControlChecked(CMainFrameControls::Panel::EDL));
}

void CMainFrame::OnEDLNewClip()
{
    if (AfxGetAppSettings().fEnableEDLEditor && (GetLoadState() == MLS::LOADED) && (GetPlaybackMode() == PM_FILE)) {
        REFERENCE_TIME rt;

        m_pMS->GetCurrentPosition(&rt);
        m_wndEditListEditor.NewClip(rt);
    }
}

void CMainFrame::OnUpdateEDLNewClip(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(m_controls.ControlChecked(CMainFrameControls::Panel::EDL));
}

void CMainFrame::OnEDLSave()
{
    if (AfxGetAppSettings().fEnableEDLEditor && (GetLoadState() == MLS::LOADED) && (GetPlaybackMode() == PM_FILE)) {
        m_wndEditListEditor.Save();
    }
}

void CMainFrame::OnUpdateEDLSave(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(m_controls.ControlChecked(CMainFrameControls::Panel::EDL));
}

// Navigation menu
void CMainFrame::OnViewNavigation()
{
    const bool bHiding = m_controls.ControlChecked(CMainFrameControls::Panel::NAVIGATION);
    m_controls.ToggleControl(CMainFrameControls::Panel::NAVIGATION);
    if (!bHiding) {
        m_wndNavigationBar.m_navdlg.UpdateElementList();
    }
    AfxGetAppSettings().fHideNavigation = bHiding;
}

void CMainFrame::OnUpdateViewNavigation(CCmdUI* pCmdUI)
{
    pCmdUI->SetCheck(m_controls.ControlChecked(CMainFrameControls::Panel::NAVIGATION));
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && GetPlaybackMode() == PM_DIGITAL_CAPTURE);
}

void CMainFrame::OnViewCapture()
{
    const bool bHiding = m_controls.ControlChecked(CMainFrameControls::Panel::CAPTURE);
    m_controls.ToggleControl(CMainFrameControls::Panel::CAPTURE);
    AfxGetAppSettings().bHideCaptureSettings = bHiding;
}

void CMainFrame::OnUpdateViewCapture(CCmdUI* pCmdUI)
{
    pCmdUI->SetCheck(m_controls.ControlChecked(CMainFrameControls::Panel::CAPTURE));
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && GetPlaybackMode() == PM_ANALOG_CAPTURE);
}

void CMainFrame::OnViewDebugShaders()
{
    auto& dlg = m_pDebugShaders;
    if (dlg && !dlg->m_hWnd) {
        // something has destroyed the dialog and we didn't know about it
        dlg = nullptr;
    }
    if (!dlg) {
        // dialog doesn't exist - create and show it
        dlg = std::make_unique<CDebugShadersDlg>();
        dlg->ShowWindow(SW_SHOW);
    } else if (dlg->IsWindowVisible()) {
        if (dlg->IsIconic()) {
            // dialog is visible but iconic - restore it
            VERIFY(dlg->ShowWindow(SW_RESTORE));
        } else {
            // dialog is visible and not iconic - destroy it
            VERIFY(dlg->DestroyWindow());
            ASSERT(!dlg->m_hWnd);
            dlg = nullptr;
        }
    } else {
        // dialog is not visible - show it
        VERIFY(!dlg->ShowWindow(SW_SHOW));
    }
}

void CMainFrame::OnUpdateViewDebugShaders(CCmdUI* pCmdUI)
{
    const auto& dlg = m_pDebugShaders;
    pCmdUI->SetCheck(dlg && dlg->m_hWnd && dlg->IsWindowVisible());
}

void CMainFrame::OnViewColorControls()
{
    auto& dlg = m_pColorControls;
    if (dlg && !dlg->m_hWnd) {
        // something has destroyed the dialog and we didn't know about it
        dlg = nullptr;
    }
    if (!dlg) {
        // dialog doesn't exist - create and show it
        dlg = std::make_unique<CColorControlsDlg>();
        dlg->ShowWindow(SW_SHOW);
    } else if (dlg->IsWindowVisible()) {
        if (dlg->IsIconic()) {
            // dialog is visible but iconic - restore it
            VERIFY(dlg->ShowWindow(SW_RESTORE));
        } else {
            // dialog is visible and not iconic - destroy it
            VERIFY(dlg->DestroyWindow());
            ASSERT(!dlg->m_hWnd);
            dlg = nullptr;
        }
    } else {
        // dialog is not visible - show it
        VERIFY(!dlg->ShowWindow(SW_SHOW));
    }
}

void CMainFrame::OnUpdateViewColorControls(CCmdUI* pCmdUI)
{
    const auto& dlg = m_pColorControls;
    pCmdUI->SetCheck(dlg && dlg->m_hWnd && dlg->IsWindowVisible());
}

void CMainFrame::OnViewMinimal()
{
    m_nActiveViewPreset = ID_VIEW_PRESETS_MINIMAL;
    SetCaptionState(MODE_BORDERLESS);
    m_controls.SetToolbarsSelection(CS_NONE, true);
}

void CMainFrame::OnUpdateViewMinimal(CCmdUI* pCmdUI)
{
}

void CMainFrame::OnViewCompact()
{
    m_nActiveViewPreset = ID_VIEW_PRESETS_COMPACT;
    SetCaptionState(MODE_FRAMEONLY);
    m_controls.SetToolbarsSelection(CS_SEEKBAR, true);
}

void CMainFrame::OnUpdateViewCompact(CCmdUI* pCmdUI)
{
}

UINT CMainFrame::GetNormalPresetCS() const
{
    return CS_SEEKBAR | CS_TOOLBAR | CS_STATUSBAR;
}

void CMainFrame::OnViewNormal()
{
    m_nActiveViewPreset = ID_VIEW_PRESETS_NORMAL;
    SetCaptionState(MODE_SHOWCAPTIONMENU);
    m_controls.SetToolbarsSelection(GetNormalPresetCS(), true);
}

void CMainFrame::ShowStatusBarForMessage()
{
    // Only relevant when the active preset hides the status bar (check the user's nCS, not the
    // effective/forced state). The bar stays revealed until the next media load.
    if ((AfxGetAppSettings().nCS & CS_STATUSBAR) || m_bStatusBarForcedForMessage) {
        return;
    }
    m_bStatusBarForcedForMessage = true;
    UpdateControlState(UPDATE_CONTROLS_VISIBILITY);
}

void CMainFrame::RestoreStatusBarMessageHold()
{
    if (m_bStatusBarForcedForMessage) {
        m_bStatusBarForcedForMessage = false;
        UpdateControlState(UPDATE_CONTROLS_VISIBILITY);
    }
}

void CMainFrame::SetClosingError(const CString& msg)
{
    m_closingmsg = msg;
    ShowStatusBarForMessage(); // reveal the status bar (if a preset hides it) so the error is visible
}

void CMainFrame::SetClosingError(UINT nIDmsg)
{
    CString msg;
    msg.LoadString(nIDmsg);
    SetClosingError(msg);
}

void CMainFrame::ApplyTimeOnSeekBarChange()
{
    // Reflect "Always"/"Never" suppression of the status-bar time and refresh the seekbar.
    m_wndStatusBar.Relayout();
    m_wndSeekBar.UpdateTime();
    m_wndSeekBar.Invalidate();
}

void CMainFrame::OnUpdateViewNormal(CCmdUI* pCmdUI)
{
}

void CMainFrame::OnViewCustom()
{
    m_nActiveViewPreset = ID_VIEW_PRESETS_CUSTOM;
    const CAppSettings& s = AfxGetAppSettings();
    SetCaptionState(static_cast<MpcCaptionState>(s.nCustomPresetCaption));
    m_controls.SetToolbarsSelection(s.nCustomPresetControlState, true);
}

void CMainFrame::OnUpdateViewCustom(CCmdUI* pCmdUI)
{
}

void CMainFrame::ApplyCustomPresetChange()
{
    // If the Custom preset is the active view, re-apply it so edits on the settings page take effect
    // immediately. Tracked explicitly (not inferred from nCS) so it still works after the user has
    // toggled an individual bar since selecting the preset (#3256).
    if (m_nActiveViewPreset == ID_VIEW_PRESETS_CUSTOM) {
        OnViewCustom();
    }
}

void CMainFrame::ApplyStartupPreset()
{
    // Applied once at launch (from InitInstance). STARTUP_PRESET_REMEMBER keeps the restored control state.
    switch (AfxGetAppSettings().nStartupPreset) {
        case STARTUP_PRESET_MINIMAL:
            OnViewMinimal();
            break;
        case STARTUP_PRESET_COMPACT:
            OnViewCompact();
            break;
        case STARTUP_PRESET_NORMAL:
            OnViewNormal();
            break;
        case STARTUP_PRESET_CUSTOM:
            OnViewCustom();
            break;
        default:
            break;
    }
}

void CMainFrame::OnViewFullscreen()
{
    const CAppSettings& s = AfxGetAppSettings();

    if (IsD3DFullScreenMode() || (s.IsD3DFullscreen() && !m_fFullScreen && !m_fAudioOnly && m_pD3DFSC && m_pMFVDC)) {
        ToggleD3DFullscreen(true);
    } else {
        ToggleFullscreen(true, true);
    }
    m_wndToolBar.SetFullscreen(m_fFullScreen);
}

void CMainFrame::OnViewFullscreenSecondary()
{
    const CAppSettings& s = AfxGetAppSettings();

    if (IsD3DFullScreenMode() || (s.IsD3DFullscreen() && !m_fFullScreen && !m_fAudioOnly && m_pD3DFSC && m_pMFVDC)) {
        ToggleD3DFullscreen(false);
    } else {
        ToggleFullscreen(true, false);
    }
    m_wndToolBar.SetFullscreen(m_fFullScreen);
}

void CMainFrame::OnUpdateViewFullscreen(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED || m_fFullScreen);
    pCmdUI->SetCheck(m_fFullScreen);
}

void CMainFrame::OnViewZoom(UINT nID)
{
    double scale = (nID == ID_VIEW_ZOOM_25) ? 0.25 : (nID == ID_VIEW_ZOOM_50) ? 0.5 : (nID == ID_VIEW_ZOOM_200) ? 2.0 : 1.0;

    ZoomVideoWindow(scale);

    CString strODSMessage;
    strODSMessage.Format(IDS_OSD_ZOOM, scale * 100);
    m_OSD.DisplayMessage(OSD_TOPLEFT, strODSMessage, 3000);
}

void CMainFrame::OnUpdateViewZoom(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly);
}

void CMainFrame::OnViewZoomAutoFit()
{
    ZoomVideoWindow(ZOOM_AUTOFIT);
    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_OSD_ZOOM_AUTO), 3000);
}

void CMainFrame::OnViewZoomAutoFitLarger()
{
    ZoomVideoWindow(ZOOM_AUTOFIT_LARGER);
    m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_OSD_ZOOM_AUTO_LARGER), 3000);
}

void CMainFrame::OnViewModifySize(UINT nID) {
    if (m_fFullScreen || !m_pVideoWnd || IsZoomed() || IsIconic() || GetLoadState() != MLS::LOADED) {
        return;
    }

    // For audio-only without custom cover art (logo or nothing), zoom is a no-op.
    if (m_fAudioOnly && !m_wndView.IsCustomImgLoaded()) {
        return;
    }

    enum resizeMethod {
        autoChoose
        , byHeight
        , byWidth
    } usedMethod;

    const CAppSettings& s = AfxGetAppSettings();

    MINMAXINFO mmi;
    CSize videoSize = GetVideoOrArtSize(mmi);
    int minWidth = (int)mmi.ptMinTrackSize.x;

    int mult = (nID == ID_VIEW_ZOOM_ADD ? 1 : ID_VIEW_ZOOM_SUB ? -1 : 0);
    double videoRatio = double(videoSize.cy) / double(videoSize.cx);

    CRect rect;
    GetWindowRect(&rect);

    CRect videoRect;
    videoRect = m_pVideoWnd->GetVideoRect();
    if (videoRect.Width() == 0) {
        if (m_fAudioOnly) {
            m_wndView.GetWindowRect(&videoRect); // art display area in screen coords
        } else {
            videoRect = rect;
        }
    }
    double videoRectRatio = double(videoRect.Height()) / double(videoRect.Width());
    bool previouslyProportional = IsNearlyEqual(videoRectRatio, videoRatio, 0.01);
    // When shrinking a non-proportional window, treat the current window shape as the
    // content ratio so both dimensions shrink together rather than only bars reducing.
    if (mult < 0 && !previouslyProportional) {
        videoRatio = videoRectRatio;
        previouslyProportional = true;
    }

    CRect workRect, maxRect;
    GetWorkAreaRect(workRect);
    maxRect = GetZoomWindowRect(CSize(INT_MAX, INT_MAX), true);

    CSize targetSize;
    CRect zoomRect;

    auto calculateZoomWindowRect = [&](resizeMethod useMethod = autoChoose, CSize forceDimension = {0,0}) {
        int newWidth = videoRect.Width();
        int newHeight = videoRect.Height();

        if (useMethod == autoChoose) {
            bool bPickByHeight;
            if (previouslyProportional) {
                // No bars (or shrinking, handled above): step by the largest dimension.
                bPickByHeight = videoRect.Height() > videoRect.Width();
            } else {
                // Bars present, growing: step toward filling them.
                // Pillarboxed (view wider than content AR) â†’ byHeight fills side bars
                // Letterboxed (view taller than content AR) â†’ byWidth fills top/bottom bars
                bPickByHeight = videoRectRatio + 0.01 < videoRatio;
            }
            if (bPickByHeight) {
                useMethod = byHeight;
                newHeight = videoRect.Height() + m_dpi.ScaleY(16) * mult;
            } else {
                useMethod = byWidth;
                newWidth = std::max(videoRect.Width() + m_dpi.ScaleX(16) * mult, minWidth);
            }
        } else if (useMethod == byHeight) {
            newHeight = forceDimension.cy + videoRect.Height() - rect.Height();
        } else {
            newWidth = forceDimension.cx + videoRect.Width() - rect.Width();
        }

        if (useMethod == byHeight) {
            double newRatio = double(newHeight) / double(videoRect.Width());
            if (s.fLimitWindowProportions || previouslyProportional || SGN(newRatio - videoRatio) != SGN(videoRectRatio - videoRatio)) {
                newWidth = std::max(int(ceil(newHeight / videoRatio)), minWidth);
                if (mult == 1) {
                    newWidth = std::max(newWidth, videoRect.Width());
                }
            }
        } else {
            double newRatio = double(videoRect.Height()) / double(newWidth);
            if (s.fLimitWindowProportions || previouslyProportional || SGN(newRatio - videoRatio) != SGN(videoRectRatio - videoRatio)) {
                newHeight = int(ceil(newWidth * videoRatio));
                if (mult == 1) {
                    newHeight = std::max(newHeight, videoRect.Height());
                }
            }
        }
        targetSize = rect.Size() + CSize(newWidth - videoRect.Width(), newHeight - videoRect.Height());
        usedMethod = useMethod;
        return GetZoomWindowRect(targetSize, true);
    };

    zoomRect = calculateZoomWindowRect();

    CRect newRect, work;
    newRect = zoomRect; //this will be our default (always constrained to work area)

    //if old rect was constrained to a single monitor, we zoom incrementally
    if (GetWorkAreaRect(work) && work.PtInRect(rect.TopLeft()) && work.PtInRect(rect.BottomRight()-CSize(1,1))
        && ((zoomRect.Height() != rect.Height() && usedMethod == byHeight) || (zoomRect.Width() != rect.Width() && usedMethod == byWidth))) {

        if (zoomRect.Width() != targetSize.cx && zoomRect.Width() == maxRect.Width()) { //we appear to have been constrained by Screen Width
            if (maxRect.Width() != rect.Width() && maxRect.Width() - rect.Width() <= m_dpi.ScaleX(32)) { //snap to fill only if we were already close to the edge
                newRect = calculateZoomWindowRect(byWidth, maxRect.Size());
            }
        } else if (zoomRect.Height() != targetSize.cy && zoomRect.Height() == maxRect.Height()) { //we appear to have been constrained by Screen Height
            if (maxRect.Height() != rect.Height() && maxRect.Height() - rect.Height() <= m_dpi.ScaleY(32)) { //snap to fill only if we were already close to the edge
                newRect = calculateZoomWindowRect(byHeight, maxRect.Size());
            }
        } else {
            newRect = zoomRect;
        }
    }

    // Step 5: if the result fills the entire work area, switch to maximized state
    // instead of a floating window that merely covers the same pixels.
    if (newRect == maxRect) {
        ShowWindow(SW_MAXIMIZE);
        return;
    }

    MoveWindow(newRect);
}

void CMainFrame::OnViewDefaultVideoFrame(UINT nID)
{
    AfxGetAppSettings().iDefaultVideoSize = nID - ID_VIEW_VF_HALF;
    m_ZoomX = m_ZoomY = 1;
    m_PosX = m_PosY = 0.5;
    MoveVideoWindow();
}

void CMainFrame::OnUpdateViewDefaultVideoFrame(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();

    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && s.iDSVideoRendererType != VIDRNDT_DS_EVR);

    int dvs = pCmdUI->m_nID - ID_VIEW_VF_HALF;
    if (s.iDefaultVideoSize == dvs && pCmdUI->m_pMenu) {
        pCmdUI->m_pMenu->CheckMenuRadioItem(ID_VIEW_VF_HALF, ID_VIEW_VF_ZOOM2, pCmdUI->m_nID, MF_BYCOMMAND);
    }
}

void CMainFrame::OnViewSwitchVideoFrame()
{
    CAppSettings& s = AfxGetAppSettings();

    int vs = s.iDefaultVideoSize;
    if (vs <= DVS_DOUBLE || vs == DVS_FROMOUTSIDE) {
        vs = DVS_STRETCH;
    } else if (vs == DVS_FROMINSIDE) {
        vs = DVS_ZOOM1;
    } else if (vs == DVS_ZOOM2) {
        vs = DVS_FROMOUTSIDE;
    } else {
        vs++;
    }
    switch (vs) { // TODO: Read messages from resource file
        case DVS_STRETCH:
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_STRETCH_TO_WINDOW));
            break;
        case DVS_FROMINSIDE:
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_TOUCH_WINDOW_FROM_INSIDE));
            break;
        case DVS_ZOOM1:
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_ZOOM1));
            break;
        case DVS_ZOOM2:
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_ZOOM2));
            break;
        case DVS_FROMOUTSIDE:
            m_OSD.DisplayMessage(OSD_TOPLEFT, ResStr(IDS_TOUCH_WINDOW_FROM_OUTSIDE));
            break;
    }
    s.iDefaultVideoSize = vs;
    m_ZoomX = m_ZoomY = 1;
    m_PosX = m_PosY = 0.5;
    MoveVideoWindow();
}

void CMainFrame::OnViewCompMonDeskARDiff()
{
    CAppSettings& s = AfxGetAppSettings();

    s.fCompMonDeskARDiff = !s.fCompMonDeskARDiff;
    OnVideoSizeChanged();
}

void CMainFrame::OnUpdateViewCompMonDeskARDiff(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();

    pCmdUI->Enable(GetLoadState() == MLS::LOADED
                   && !m_fAudioOnly
                   && s.iDSVideoRendererType != VIDRNDT_DS_EVR
                   // This doesn't work with madVR due to the fact that it positions video itself.
                   // And it has exactly the same option built in.
                   && s.iDSVideoRendererType != VIDRNDT_DS_MADVR);
    pCmdUI->SetCheck(s.fCompMonDeskARDiff);
}

void CMainFrame::OnViewPanNScan(UINT nID)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    int x = 0, y = 0;
    int dx = 0, dy = 0;

    switch (nID) {
        case ID_VIEW_RESET:
            // Subtitle overrides
            ResetSubtitlePosAndSize(true);
            // Pan&Scan
            m_ZoomX = m_ZoomY = 1.0;
            m_PosX = m_PosY = 0.5;
            m_AngleX = m_AngleY = m_AngleZ = 0;
            PerformFlipRotate();
            break;
        case ID_VIEW_INCSIZE:
            x = y = 1;
            break;
        case ID_VIEW_DECSIZE:
            x = y = -1;
            break;
        case ID_VIEW_INCWIDTH:
            x = 1;
            break;
        case ID_VIEW_DECWIDTH:
            x = -1;
            break;
        case ID_VIEW_INCHEIGHT:
            y = 1;
            break;
        case ID_VIEW_DECHEIGHT:
            y = -1;
            break;
        case ID_PANSCAN_CENTER:
            m_PosX = m_PosY = 0.5;
            break;
        case ID_PANSCAN_MOVELEFT:
            dx = -1;
            break;
        case ID_PANSCAN_MOVERIGHT:
            dx = 1;
            break;
        case ID_PANSCAN_MOVEUP:
            dy = -1;
            break;
        case ID_PANSCAN_MOVEDOWN:
            dy = 1;
            break;
        case ID_PANSCAN_MOVEUPLEFT:
            dx = dy = -1;
            break;
        case ID_PANSCAN_MOVEUPRIGHT:
            dx = 1;
            dy = -1;
            break;
        case ID_PANSCAN_MOVEDOWNLEFT:
            dx = -1;
            dy = 1;
            break;
        case ID_PANSCAN_MOVEDOWNRIGHT:
            dx = dy = 1;
            break;
        default:
            break;
    }

    if (x > 0 && m_ZoomX < 5.0) {
        m_ZoomX = std::min(m_ZoomX * 1.02, 5.0);
    } else if (x < 0 && m_ZoomX > 0.2) {
        m_ZoomX = std::max(m_ZoomX / 1.02, 0.2);
    }

    if (y > 0 && m_ZoomY < 5.0) {
        m_ZoomY = std::min(m_ZoomY * 1.02, 5.0);
    } else if (y < 0 && m_ZoomY > 0.2) {
        m_ZoomY = std::max(m_ZoomY / 1.02, 0.2);
    }

    if (dx < 0 && m_PosX > -0.5) {
        m_PosX = std::max(m_PosX - 0.005 * m_ZoomX, -0.5);
    } else if (dx > 0 && m_PosX < 1.5) {
        m_PosX = std::min(m_PosX + 0.005 * m_ZoomX, 1.5);
    }

    if (dy < 0 && m_PosY > -0.5) {
        m_PosY = std::max(m_PosY - 0.005 * m_ZoomY, -0.5);
    } else if (dy > 0 && m_PosY < 1.5) {
        m_PosY = std::min(m_PosY + 0.005 * m_ZoomY, 1.5);
    }

    MoveVideoWindow(true);
}

void CMainFrame::OnUpdateViewPanNScan(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && AfxGetAppSettings().iDSVideoRendererType != VIDRNDT_DS_EVR);
}

void CMainFrame::ApplyPanNScanPresetString()
{
    auto& s = AfxGetAppSettings();

    if (s.strPnSPreset.IsEmpty())
        return;

    if (s.strPnSPreset.Find(',') != -1) { // try to set raw values
        if (_stscanf_s(s.strPnSPreset, _T("%lf,%lf,%lf,%lf"), &m_PosX, &m_PosY, &m_ZoomX, &m_ZoomY) == 4) {
            ValidatePanNScanParameters();
            MoveVideoWindow();
        }
    } else { // try to set named preset
        for (int i = 0; i < s.m_pnspresets.GetCount(); i++) {
            int j = 0;
            CString str = s.m_pnspresets[i];
            CString label = str.Tokenize(_T(","), j);
            if (s.strPnSPreset == label) {
                OnViewPanNScanPresets(i + ID_PANNSCAN_PRESETS_START);
            }
        }
    }

    s.strPnSPreset.Empty();
}

void CMainFrame::OnViewPanNScanPresets(UINT nID)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    CAppSettings& s = AfxGetAppSettings();

    nID -= ID_PANNSCAN_PRESETS_START;

    if ((INT_PTR)nID == s.m_pnspresets.GetCount()) {
        CPnSPresetsDlg dlg;
        dlg.m_pnspresets.Copy(s.m_pnspresets);
        if (dlg.DoModal() == IDOK) {
            s.m_pnspresets.Copy(dlg.m_pnspresets);
            s.SaveSettings();
        }
        return;
    }

    m_PosX = 0.5;
    m_PosY = 0.5;
    m_ZoomX = 1.0;
    m_ZoomY = 1.0;

    CString str = s.m_pnspresets[nID];

    int i = 0, j = 0;
    for (CString token = str.Tokenize(_T(","), i); !token.IsEmpty(); token = str.Tokenize(_T(","), i), j++) {
        float f = 0;
        if (_stscanf_s(token, _T("%f"), &f) != 1) {
            continue;
        }

        switch (j) {
            case 0:
                break;
            case 1:
                m_PosX = f;
                break;
            case 2:
                m_PosY = f;
                break;
            case 3:
                m_ZoomX = f;
                break;
            case 4:
                m_ZoomY = f;
                break;
            default:
                break;
        }
    }

    if (j != 5) {
        return;
    }

    ValidatePanNScanParameters();

    MoveVideoWindow(true);
}

void CMainFrame::ValidatePanNScanParameters()
{
    m_PosX = std::min(std::max(m_PosX, -0.5), 1.5);
    m_PosY = std::min(std::max(m_PosY, -0.5), 1.5);
    m_ZoomX = std::min(std::max(m_ZoomX, 0.2), 5.0);
    m_ZoomY = std::min(std::max(m_ZoomY, 0.2), 5.0);
}

void CMainFrame::OnUpdateViewPanNScanPresets(CCmdUI* pCmdUI)
{
    int nID = pCmdUI->m_nID - ID_PANNSCAN_PRESETS_START;
    const CAppSettings& s = AfxGetAppSettings();
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && nID >= 0 && nID <= s.m_pnspresets.GetCount() && s.iDSVideoRendererType != VIDRNDT_DS_EVR);
}

int nearest90(int angle) {
    return int(float(angle) / 90 + 0.5) * 90;
}

bool CMainFrame::PerformFlipRotate()
{
    HRESULT hr = E_NOTIMPL;
    // Note: m_AngleZ is counterclockwise, so value 270 means rotated 90 degrees clockwise
    if (m_pCAP3) {
        int rotation = (360 - m_AngleZ + m_iDefRotation) % 360;
        if (m_pMVRS) { // MadVR
            bool isFlip = m_AngleX == 180;
            // MadVR does not support mirror, instead of flip we rotate 180 degrees
            hr = m_pCAP3->SetRotation(isFlip ? (rotation + 180) % 360 : rotation);
        } else { // MPCVR
            bool isFlip, isMirror;
            if (m_iDefRotation == 90 || m_iDefRotation == 270) {
                isFlip   = m_AngleY == 180;
                isMirror = m_AngleX == 180;
            } else {
                isFlip   = m_AngleX == 180;
                isMirror = m_AngleY == 180;
            }
            // MPCVR: instead of flip, we mirror plus rotate 180 degrees
            hr = m_pCAP3->SetRotation(isFlip ? (rotation + 180) % 360 : rotation);
            if (SUCCEEDED(hr)) {
                // SetFlip actually mirrors instead of doing vertical flip
                hr = m_pCAP3->SetFlip(isFlip || isMirror);
            }
        }
    } else if (m_pCAP) {
        // EVR-CP behavior for custom angles is ignored when choosing video size and zoom
        // We get better results if we treat the closest 90 as the standard rotation, and custom rotate the remainder (<45deg)
        int z = m_AngleZ;
        if (m_pCAP2) {
            int nZ = nearest90(z);
            z = (z - nZ + 360) % 360;
            Vector defAngle = Vector(0, 0, Vector::DegToRad((nZ - m_iDefRotation + 360) % 360));
            m_pCAP2->SetDefaultVideoAngle(defAngle);
        }
        
        hr = m_pCAP->SetVideoAngle(Vector(Vector::DegToRad(m_AngleX), Vector::DegToRad(m_AngleY), Vector::DegToRad(z)));
    }

    if (FAILED(hr)) {
        m_AngleX = m_AngleY = m_AngleZ = 0;
        return false;
    }
    if (m_pCAP2_preview) { //we support rotating preview
        PreviewWindowHide();
        m_wndPreView.SetWindowSize();
        SetPreviewVideoPosition();
        //adipose: using defaultvideoangle instead of videoangle, as some oddity with AR shows up when using normal rotate with EVRCP.
        //Since we only need to support 4 angles, this will work, but it *should* work with SetVideoAngle...

        hr = m_pCAP2_preview->SetDefaultVideoAngle(Vector(Vector::DegToRad(nearest90(m_AngleX)), Vector::DegToRad(nearest90(m_AngleY)), Vector::DegToRad(defaultVideoAngle + nearest90(m_AngleZ))));
    }

    return true;
}

void CMainFrame::OnViewRotate(UINT nID)
{
    switch (nID) {
    case ID_PANSCAN_ROTATEXP:
        if (!m_pCAP3) {
            m_AngleX += 2;
            break;
        }
        [[fallthrough]]; // fall through for m_pCAP3
    case ID_PANSCAN_ROTATEXM:
        if (m_AngleX >= 180) {
            m_AngleX = 0;
        } else {
            m_AngleX = 180;
        }
        break;
    case ID_PANSCAN_ROTATEYP:
        if (!m_pCAP3) {
            m_AngleY += 2;
            break;
        }
        [[fallthrough]];
    case ID_PANSCAN_ROTATEYM:
        if (m_AngleY >= 180) {
            m_AngleY = 0;
        } else {
            m_AngleY = 180;
        }
        break;
    case ID_PANSCAN_ROTATEZM:
        if (m_AngleZ == 0 || m_AngleZ > 270) {
            m_AngleZ = 270;
        } else if (m_AngleZ > 180) {
            m_AngleZ = 180;
        } else if (m_AngleZ > 90) {
            m_AngleZ = 90;
        } else if (m_AngleZ > 0) {
            m_AngleZ = 0;
        }
        break;
    case ID_PANSCAN_ROTATEZP2:
        if (!m_pCAP3) {
            m_AngleZ += 2;
            break;
        }
        [[fallthrough]];
    case ID_PANSCAN_ROTATEZ270:
    case ID_PANSCAN_ROTATEZ270_OLD:
        if (m_AngleZ < 90) {
            m_AngleZ = 90;
        } else if (m_AngleZ >= 270) {
            m_AngleZ = 0;
        } else if (m_AngleZ >= 180) {
            m_AngleZ = 270;
        } else if (m_AngleZ >= 90) {
            m_AngleZ = 180;
        }
        break;
    default:
        return;
    }

    m_AngleX %= 360;
    m_AngleY %= 360;
    if (m_AngleX == 180 && m_AngleY == 180) {
        m_AngleX = m_AngleY = 0;
        m_AngleZ += 180;
    }
    m_AngleZ %= 360;

    ASSERT(m_AngleX >= 0);
    ASSERT(m_AngleY >= 0);
    ASSERT(m_AngleZ >= 0);

    if (PerformFlipRotate()) {
        // FIXME: do proper resizing of the window after rotate
        if (!m_pMVRC) {
            MoveVideoWindow();
        }

        CString info;
        info.Format(_T("x: %d, y: %d, z: %d"), m_AngleX, m_AngleY, m_AngleZ);
        SendStatusMessage(info, 3000);
    }
}

void CMainFrame::OnUpdateViewRotate(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && (m_pCAP || m_pCAP3));
}

// FIXME
const static SIZE s_ar[] = {{0, 0}, {4, 3}, {5, 4}, {16, 9}, {235, 100}, {185, 100}};

void CMainFrame::OnViewAspectRatio(UINT nID)
{
    auto& s = AfxGetAppSettings();

    CString info;
    if (nID == ID_ASPECTRATIO_SAR) {
        s.fKeepAspectRatio = false;
        info.LoadString(IDS_ASPECT_RATIO_SAR);
    } else {
        s.fKeepAspectRatio = true;
        CSize ar = s_ar[nID - ID_ASPECTRATIO_START];
        s.SetAspectRatioOverride(ar);
        if (ar.cx && ar.cy) {
            info.Format(IDS_MAINFRM_68, ar.cx, ar.cy);
        } else {
            info.LoadString(IDS_MAINFRM_69);
        }
    }

    SendStatusMessage(info, 3000);
    m_OSD.DisplayMessage(OSD_TOPLEFT, info, 3000);

    OnVideoSizeChanged();
}

void CMainFrame::OnUpdateViewAspectRatio(CCmdUI* pCmdUI)
{
    const CAppSettings& s = AfxGetAppSettings();

    bool bSelected;
    if (pCmdUI->m_nID == ID_ASPECTRATIO_SAR) {
        bSelected = s.fKeepAspectRatio == false;
    } else {
        bSelected = s.fKeepAspectRatio == true && s.GetAspectRatioOverride() == s_ar[pCmdUI->m_nID - ID_ASPECTRATIO_START];
    }
    if (bSelected && pCmdUI->m_pMenu) {
        pCmdUI->m_pMenu->CheckMenuRadioItem(ID_ASPECTRATIO_START, ID_ASPECTRATIO_END, pCmdUI->m_nID, MF_BYCOMMAND);
    }

    pCmdUI->Enable(GetLoadState() == MLS::LOADED && !m_fAudioOnly && s.iDSVideoRendererType != VIDRNDT_DS_EVR);
}

void CMainFrame::OnViewAspectRatioNext()
{
    static_assert(ID_ASPECTRATIO_SAR - ID_ASPECTRATIO_START == _countof(s_ar) && ID_ASPECTRATIO_SAR == ID_ASPECTRATIO_END,
                  "ID_ASPECTRATIO_SAR needs to be last item in the menu.");

    const auto& s = AfxGetAppSettings();
    UINT nID = ID_ASPECTRATIO_START;
    if (s.fKeepAspectRatio) {
        const CSize ar = s.GetAspectRatioOverride();
        for (int i = 0; i < _countof(s_ar); i++) {
            if (ar == s_ar[i]) {
                nID += (i + 1) % ((ID_ASPECTRATIO_END - ID_ASPECTRATIO_START) + 1);
                break;
            }
        }
    }

    OnViewAspectRatio(nID);
}

void CMainFrame::OnViewOntop(UINT nID)
{
    nID -= ID_ONTOP_DEFAULT;
    if (AfxGetAppSettings().iOnTop == (int)nID) {
        nID = !nID;
    }
    SetAlwaysOnTop(nID);
}

void CMainFrame::OnUpdateViewOntop(CCmdUI* pCmdUI)
{
    int onTop = pCmdUI->m_nID - ID_ONTOP_DEFAULT;
    if (AfxGetAppSettings().iOnTop == onTop && pCmdUI->m_pMenu) {
        pCmdUI->m_pMenu->CheckMenuRadioItem(ID_ONTOP_DEFAULT, ID_ONTOP_WHILEPLAYINGVIDEO, pCmdUI->m_nID, MF_BYCOMMAND);
    }
}

void CMainFrame::OnViewOptions()
{
    ShowOptions();
}

// play

void CMainFrame::OnPlayPlay()
{
    const CAppSettings& s = AfxGetAppSettings();

    m_timerOneTime.Unsubscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE);
    m_bOpeningInAutochangedMonitorMode = false;
    m_bPausedForAutochangeMonitorMode = false;

    if (!IsStateClosedOrLoaded()) {
        return;
    }

    if (IsStateClosed()) {
        m_bFirstPlay = false;
        OpenCurPlaylistItem();
        return;
    }

    if (IsStateLoaded()) {
        // If playback was previously stopped or ended, we need to reset the window size
        bool bVideoWndNeedReset = GetMediaState() == State_Stopped || m_fEndOfStream;
        bool still_image = !m_bFirstPlay && !m_fAudioOnly && !m_wndSeekBar.HasDuration() && m_wndStatusBar.GetTimerCurPos() == 0LL && GetPlaybackMode() == PM_FILE && IsImageFile(lastOpenFile);

        KillTimersStop();

        if (GetPlaybackMode() == PM_FILE) {
            if (still_image) {
                // images need to be reloaded
                if (bVideoWndNeedReset) {
                    OnFileReopen();
                }
                return;
            }
            if (!m_bFirstPlay && !m_fAudioOnly && m_wndSeekBar.HasDuration() && m_dwLastPause && s.iReloadAfterLongPause > 0) {
                // after long pause reload video file to avoid playback issues on some systems (with buggy drivers)
                if (GetTickCount64() - m_dwLastPause >= s.iReloadAfterLongPause * 60 * 1000ULL) {
                    m_reloadFilename = lastOpenFile;
                    m_rtReloadPos = m_fEndOfStream ? 0LL : m_wndSeekBar.GetPos();
                    reloadABRepeat = abRepeat;
                    m_iReloadAudioIdx = GetCurrentAudioTrackIdx();
                    m_iReloadSubIdx = GetCurrentSubtitleTrackIdx();
                    OnFileReopen();
                    return;
                }
            }
            if (m_fEndOfStream) {
                SendMessage(WM_COMMAND, ID_PLAY_STOP);
            }
            if (m_pMS) {
                if (FAILED(m_pMS->SetRate(m_dSpeedRate))) {
                    m_dSpeedRate = 1.0;
                }
            }
        } else if (GetPlaybackMode() == PM_DVD) {
            m_dSpeedRate = 1.0;
            m_pDVDC->PlayForwards(m_dSpeedRate, DVD_CMD_FLAG_Block, nullptr);
            m_pDVDC->Pause(FALSE);
        } else if (GetPlaybackMode() == PM_ANALOG_CAPTURE) {
            MediaControlStop(); // audio preview won't be in sync if we run it from paused state
        } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
            CComQIPtr<IBDATuner> pTun = m_pGB;
            if (pTun) {
                bVideoWndNeedReset = false; // SetChannel deals with MoveVideoWindow
                SetChannel(s.nDVBLastChannel);
            } else {
                ASSERT(FALSE);
            }
        } else {
            ASSERT(FALSE);
        }

        if (bVideoWndNeedReset) {
            MoveVideoWindow(false, true);
        }

        if (m_fFrameSteppingActive) {
            if (m_pFS.p) {
                m_pFS->CancelStep();
            }
            m_fFrameSteppingActive = false;
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
        } else {
            if (m_pBA) {
                m_pBA->put_Volume(m_wndToolBar.Volume);
            }
        }
        m_nStepForwardCount = 0;

        // Restart playback
        MediaControlRun();

        SetAlwaysOnTop(s.iOnTop);

        SetTimersPlay();
    }

    m_Lcd.SetStatusMessage(ResStr(IDS_CONTROLS_PLAYING), 3000);
    SetPlayState(PS_PLAY);

    OnTimer(TIMER_STREAMPOSPOLLER);

    SetupEVRColorControl(); // can be configured when streaming begins

    if (m_OSD.CanShowMessage()) {
        CString strOSD;
        CString strPlay(StrRes(ID_PLAY_PLAY));
        int i = strPlay.Find(_T("\n"));
        if (i > 0) {
            strPlay.Delete(i, strPlay.GetLength() - i);
        }

        if (m_bFirstPlay) {
            if (GetPlaybackMode() == PM_FILE) {
                if (!m_LastOpenBDPath.IsEmpty()) {
                    strOSD.LoadString(IDS_PLAY_BD);
                } else {
                    strOSD = GetFileName();
                    CPlaylistItem pli;
                    if (!strOSD.IsEmpty() && (!m_wndPlaylistBar.GetCur(pli) || !pli.m_bYoutubeDL)) {
                        strOSD.TrimRight('/');
                        strOSD.Replace('\\', '/');
                        strOSD = strOSD.Mid(strOSD.ReverseFind('/') + 1);
                    }
                }
            } else if (GetPlaybackMode() == PM_DVD) {
                strOSD.LoadString(IDS_PLAY_DVD);
            }
        }

        if (strOSD.IsEmpty()) {
            strOSD = strPlay;
        }
        if (GetPlaybackMode() != PM_DIGITAL_CAPTURE) {
            m_OSD.DisplayMessage(OSD_TOPLEFT, strOSD, 3000);
        }
    }

    m_bFirstPlay = false;
}

void CMainFrame::OnPlayPause()
{
    m_timerOneTime.Unsubscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE);
    m_bOpeningInAutochangedMonitorMode = false;

    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (GetMediaState() == State_Stopped) {
        MoveVideoWindow(false, true);
    }

    if (GetPlaybackMode() == PM_FILE || GetPlaybackMode() == PM_DVD || GetPlaybackMode() == PM_ANALOG_CAPTURE) {
        if (m_fFrameSteppingActive) {
            m_pFS->CancelStep();
            m_fFrameSteppingActive = false;
            m_nStepForwardCount = 0;
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
        }
        MediaControlPause(true);
    }

    KillTimer(TIMER_STATS);
    SetAlwaysOnTop(AfxGetAppSettings().iOnTop);

    CString strOSD(StrRes(ID_PLAY_PAUSE));
    int i = strOSD.Find(_T("\n"));
    if (i > 0) {
        strOSD.Delete(i, strOSD.GetLength() - i);
    }
    m_OSD.DisplayMessage(OSD_TOPLEFT, strOSD, 3000);
    m_Lcd.SetStatusMessage(ResStr(IDS_CONTROLS_PAUSED), 3000);
    SetPlayState(PS_PAUSE);
}

void CMainFrame::OnPlayPlaypause()
{
    if (GetLoadState() == MLS::LOADED) {
        OAFilterState fs = GetMediaState();
        if (fs == State_Running) {
            PostMessage(WM_COMMAND, ID_PLAY_PAUSE);
        } else if (fs == State_Stopped || fs == State_Paused) {
            PostMessage(WM_COMMAND, ID_PLAY_PLAY);
        }
    } else if (GetLoadState() == MLS::CLOSED && !IsPlaylistEmpty()) {
        PostMessage(WM_COMMAND, ID_PLAY_PLAY);        
    }
}

void CMainFrame::OnApiPause()
{
    OAFilterState fs = GetMediaState();
    if (fs == State_Running) {
        PostMessage(WM_COMMAND, ID_PLAY_PAUSE);
    }
}
void CMainFrame::OnApiPlay()
{
    OAFilterState fs = GetMediaState();
    if (fs == State_Stopped || fs == State_Paused) {
        PostMessage(WM_COMMAND, ID_PLAY_PLAY);
    }
}

void CMainFrame::OnPlayStop()
{
    OnPlayStop(false);
}

void CMainFrame::OnPlayStop(bool is_closing)
{
    m_timerOneTime.Unsubscribe(TimerOneTimeSubscriber::DELAY_PLAYPAUSE_AFTER_AUTOCHANGE_MODE);
    m_bOpeningInAutochangedMonitorMode = false;
    m_bPausedForAutochangeMonitorMode = false;

    KillTimersStop();

    m_wndSeekBar.SetPos(0);
    if (GetLoadState() == MLS::LOADED) {
        if (GetPlaybackMode() == PM_FILE) {
            if (!is_closing) {
                LONGLONG pos = 0;
                m_pMS->SetPositions(&pos, AM_SEEKING_AbsolutePositioning, nullptr, AM_SEEKING_NoPositioning);
            }
            MediaControlStop(true);
            if (m_bUseSeekPreview) {
                MediaControlStopPreview();
            }

            if (!is_closing && m_pAMNS && m_pFSF) {
                CComQIPtr<IBaseFilter> pBF = m_pFSF;
                if (pBF) {
                    CLSID clsid = GetCLSID(pBF);
                    if (clsid == CLSID_NetShowSource) {
                        // After pause or stop the netshow url source filter won't continue
                        // on the next play command, unless we cheat it by setting the file name again.
                        WCHAR* pFN = nullptr;
                        AM_MEDIA_TYPE mt;
                        if (SUCCEEDED(m_pFSF->GetCurFile(&pFN, &mt)) && pFN && *pFN) {
                            m_pFSF->Load(pFN, nullptr);
                            CoTaskMemFree(pFN);
                        }
                    }
                }
            }
        } else if (GetPlaybackMode() == PM_DVD) {
            m_pDVDC->SetOption(DVD_ResetOnStop, TRUE);
            MediaControlStop(true);
            m_pDVDC->SetOption(DVD_ResetOnStop, FALSE);

            if (m_bUseSeekPreview && m_pDVDC_preview) {
                m_pDVDC_preview->SetOption(DVD_ResetOnStop, TRUE);
                MediaControlStopPreview();
                m_pDVDC_preview->SetOption(DVD_ResetOnStop, FALSE);
            }
        } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
            MediaControlStop(true);
            m_pDVBState->bActive = false;
            OpenSetupWindowTitle();
            m_wndStatusBar.SetStatusTimer(StrRes(IDS_CAPTURE_LIVE));
        } else if (GetPlaybackMode() == PM_ANALOG_CAPTURE) {
            MediaControlStop(true);
        }

        if (!m_fEndOfStream) {
            m_dSpeedRate = 1.0;
        }

        if (m_fFrameSteppingActive) {
            m_pFS->CancelStep();
            m_fFrameSteppingActive = false;
            m_nStepForwardCount = 0;
            if (m_pBA) {
                m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
            }
        }
        m_nStepForwardCount = 0;
    } else if (GetLoadState() == MLS::CLOSING) {
        // graph will be stopped in CloseMediaPrivate()
    }

    m_nLoops = 0;

    if (!is_closing && m_hWnd) {
        MoveVideoWindow();

        if (GetLoadState() == MLS::LOADED) {
            __int64 start, stop;
            m_wndSeekBar.GetRange(start, stop);
            if (!IsPlaybackCaptureMode()) {
                m_wndStatusBar.SetStatusTimer(m_wndSeekBar.GetPos(), stop, IsSubresyncBarVisible(), GetTimeFormat());
            }

            SetAlwaysOnTop(AfxGetAppSettings().iOnTop);
        }
    }

    if (!is_closing && !m_fEndOfStream && GetLoadState() == MLS::LOADED) {
        CString strOSD(StrRes(ID_PLAY_STOP));
        int i = strOSD.Find(_T("\n"));
        if (i > 0) {
            strOSD.Delete(i, strOSD.GetLength() - i);
        }
        m_OSD.DisplayMessage(OSD_TOPLEFT, strOSD, 3000);
        m_Lcd.SetStatusMessage(ResStr(IDS_CONTROLS_STOPPED), 3000);
    } else {
        m_fEndOfStream = false;
    }

    SetPlayState(PS_STOP);
}

void CMainFrame::OnUpdatePlayPauseStop(CCmdUI* pCmdUI)
{
    bool fEnable = false;
    bool fCheck = false;

    if (GetLoadState() == MLS::LOADED) {
        OAFilterState fs = m_fFrameSteppingActive ? State_Paused : GetMediaState();

        fCheck = pCmdUI->m_nID == ID_PLAY_PLAY && fs == State_Running ||
            pCmdUI->m_nID == ID_PLAY_PAUSE && fs == State_Paused ||
            pCmdUI->m_nID == ID_PLAY_STOP && fs == State_Stopped ||
            pCmdUI->m_nID == ID_PLAY_PLAYPAUSE && (fs == State_Paused || fs == State_Running);

        if (pCmdUI->m_nID == ID_PLAY_PLAY) {
            if (fs == State_Running) {
                m_wndToolBar.SetPlayPauseActiveButton(ID_PLAY_PAUSE);
            } else {
                m_wndToolBar.SetPlayPauseActiveButton(ID_PLAY_PLAY);
            }
        }

        if (fs >= 0) {
            if (GetPlaybackMode() == PM_FILE || IsPlaybackCaptureMode()) {
                fEnable = true;

                if (m_fCapturing) {
                    fEnable = false;
                } else if (m_fLiveWM && pCmdUI->m_nID == ID_PLAY_PAUSE) {
                    fEnable = false;
                } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE && pCmdUI->m_nID == ID_PLAY_PAUSE) {
                    fEnable = false; // Disable pause for digital capture mode to avoid accidental playback stop. We don't support time shifting yet.
                }
            } else if (GetPlaybackMode() == PM_DVD) {
                fEnable = m_iDVDDomain != DVD_DOMAIN_VideoManagerMenu
                    && m_iDVDDomain != DVD_DOMAIN_VideoTitleSetMenu;

                if (fs == State_Stopped && pCmdUI->m_nID == ID_PLAY_PAUSE) {
                    fEnable = false;
                }
            }
        }
    } else if (GetLoadState() == MLS::CLOSED) {
        fEnable = (pCmdUI->m_nID == ID_PLAY_PLAY || pCmdUI->m_nID == ID_PLAY_PLAYPAUSE) && !IsPlaylistEmpty();

        if (pCmdUI->m_nID == ID_PLAY_PLAY) {
            // Ensure play button is visible when no media is loaded
            m_wndToolBar.SetPlayPauseActiveButton(ID_PLAY_PLAY);
        }
    }

    pCmdUI->SetCheck(fCheck);
    pCmdUI->Enable(fEnable);
}

void CMainFrame::OnPlayFramestep(UINT nID)
{
    if (!m_pFS && !m_pMS || m_fAudioOnly || GetLoadState() != MLS::LOADED || GetPlaybackMode() != PM_FILE && GetPlaybackMode() != PM_DVD) {
        return;
    }

    KillTimerDelayedSeek();

    m_OSD.EnableShowMessage(false);

    if (m_CachedFilterState == State_Paused) {
        // Double check the state, because graph may have silently gone into a running state after performing a framestep
        if (UpdateCachedMediaState() != State_Paused) {
            MediaControlPause(true);
        }
    } else {
        KillTimer(TIMER_STATS);
        MediaControlPause(true);
    }

    if (nID == ID_PLAY_FRAMESTEP && m_pFS) {
        // To support framestep back, store the initial position when
        // stepping forward
        if (m_nStepForwardCount == 0) {
            if (GetPlaybackMode() == PM_DVD) {
                OnTimer(TIMER_STREAMPOSPOLLER);
                m_rtStepForwardStart = m_wndSeekBar.GetPos();
            } else {
                m_pMS->GetCurrentPosition(&m_rtStepForwardStart);
            }
        }

        if (!m_fFrameSteppingActive) {
            m_fFrameSteppingActive = true;
            m_nVolumeBeforeFrameStepping = m_wndToolBar.Volume;
            if (m_pBA) {
                m_pBA->put_Volume(-10000);
            }
        }

       HRESULT hr = m_pFS->Step(1, nullptr);
       if (FAILED(hr)) {
           TRACE(_T("Frame step failed.\n"));
           m_fFrameSteppingActive = false;
           m_nStepForwardCount = 0;
           if (m_pBA) {
               m_pBA->put_Volume(m_nVolumeBeforeFrameStepping);
           }
       }
    } else if (m_pMS && (m_nStepForwardCount == 0) && (S_OK == m_pMS->IsFormatSupported(&TIME_FORMAT_FRAME))) {
        if (SUCCEEDED(m_pMS->SetTimeFormat(&TIME_FORMAT_FRAME))) {
            REFERENCE_TIME rtCurPos;

            if (SUCCEEDED(m_pMS->GetCurrentPosition(&rtCurPos))) {
                rtCurPos += (nID == ID_PLAY_FRAMESTEP) ? 1 : -1;

                m_pMS->SetPositions(&rtCurPos, AM_SEEKING_AbsolutePositioning, nullptr, AM_SEEKING_NoPositioning);
            }
            m_pMS->SetTimeFormat(&TIME_FORMAT_MEDIA_TIME);
        }
    } else { // nID == ID_PLAY_FRAMESTEP_BACK
        const REFERENCE_TIME rtAvgTimePerFrame = std::llround(GetAvgTimePerFrame() * 10000000LL);
        REFERENCE_TIME rtCurPos = 0;
        
        if (m_nStepForwardCount) { // Exit of framestep forward, calculate current position
            m_pFS->CancelStep();
            rtCurPos = m_rtStepForwardStart + m_nStepForwardCount * rtAvgTimePerFrame;
            m_nStepForwardCount = 0;
            rtCurPos -= rtAvgTimePerFrame;
        } else if (GetPlaybackMode() == PM_DVD) {
            // IMediaSeeking doesn't work properly with DVD Navigator
            // Unfortunately, IDvdInfo2::GetCurrentLocation is inaccurate as well and only updates position approx. once per 500ms
            // Due to inaccurate start position value, framestep backwards simply doesn't work well with DVDs.
            // Seeking has same accuracy problem. Best we can do is jump back 500ms to at least get to a different frame.
            OnTimer(TIMER_STREAMPOSPOLLER);
            rtCurPos = m_wndSeekBar.GetPos();
            rtCurPos -= 5000000LL;
        } else {
            m_pMS->GetCurrentPosition(&rtCurPos);
            rtCurPos -= rtAvgTimePerFrame;
        }

        DoSeekTo(rtCurPos, false);
    }
    m_OSD.EnableShowMessage();
}

void CMainFrame::OnUpdatePlayFramestep(CCmdUI* pCmdUI)
{
    bool fEnable = false;

    if (pCmdUI->m_nID == ID_PLAY_FRAMESTEP) {
        if (!m_fAudioOnly && !m_fLiveWM && GetLoadState() == MLS::LOADED && (GetPlaybackMode() == PM_FILE || (GetPlaybackMode() == PM_DVD && m_iDVDDomain == DVD_DOMAIN_Title))) {
            if (m_pFS || m_pMS && (S_OK == m_pMS->IsFormatSupported(&TIME_FORMAT_FRAME))) {
                fEnable = true;
            }
        }
    }
    pCmdUI->Enable(fEnable);
}

void CMainFrame::OnPlaySeek(UINT nID)
{
    const auto& s = AfxGetAppSettings();

    REFERENCE_TIME rtJumpDiff =
        nID == ID_PLAY_SEEKBACKWARDSMALL ? -10000i64 * s.nJumpDistS :
        nID == ID_PLAY_SEEKFORWARDSMALL  ? +10000i64 * s.nJumpDistS :
        nID == ID_PLAY_SEEKBACKWARDMED   ? -10000i64 * s.nJumpDistM :
        nID == ID_PLAY_SEEKFORWARDMED    ? +10000i64 * s.nJumpDistM :
        nID == ID_PLAY_SEEKBACKWARDLARGE ? -10000i64 * s.nJumpDistL :
        nID == ID_PLAY_SEEKFORWARDLARGE  ? +10000i64 * s.nJumpDistL :
        0;

    if (rtJumpDiff == 0) {
        ASSERT(FALSE);
        return;
    }

    if (m_fShockwaveGraph) {
        // HACK: the custom graph should support frame based seeking instead
        rtJumpDiff /= 10000i64 * 100;
    }

    const REFERENCE_TIME rtPos = m_wndSeekBar.GetPos();
    REFERENCE_TIME rtSeekTo = rtPos + rtJumpDiff;
    if (rtSeekTo < 0) {
        rtSeekTo = 0;
    }

    if (s.bFastSeek && !m_kfs.empty()) {
        REFERENCE_TIME rtMaxForwardDiff;
        REFERENCE_TIME rtMaxBackwardDiff;
        if (s.bAllowInaccurateFastseek && (s.nJumpDistS >= 5000 || (nID != ID_PLAY_SEEKBACKWARDSMALL) && (nID != ID_PLAY_SEEKFORWARDSMALL))) {
            if (rtJumpDiff > 0) {
                rtMaxForwardDiff  = 200000000LL;
                rtMaxBackwardDiff = rtJumpDiff / 2;
            } else {
                rtMaxForwardDiff  = -rtJumpDiff / 2;
                rtMaxBackwardDiff = 200000000LL;
            }
        } else {
            rtMaxForwardDiff = rtMaxBackwardDiff = std::min(100000000LL, abs(rtJumpDiff) * 3 / 10);
        }
        rtSeekTo = GetClosestKeyFrame(rtSeekTo, rtMaxForwardDiff, rtMaxBackwardDiff);
    }

    SeekTo(rtSeekTo);
}

void CMainFrame::OnPlaySeekSet()
{
    const REFERENCE_TIME rtPos = m_wndSeekBar.GetPos();
    REFERENCE_TIME rtStart, rtStop;
    m_wndSeekBar.GetRange(rtStart, rtStop);

    if (abRepeat.positionA > rtStart && abRepeat.positionA < rtStop) {
        rtStart = abRepeat.positionA;
    }
    if (rtPos != rtStart) {
        SeekTo(rtStart, false);
    }
}

void CMainFrame::AdjustStreamPosPoller(bool restart)
{
    int current_value = m_iStreamPosPollerInterval;

    if (g_bExternalSubtitleTime || IsSubresyncBarVisible()) {
        m_iStreamPosPollerInterval = 40;
    } else {
        m_iStreamPosPollerInterval = AfxGetAppSettings().nStreamPosPollerInterval;
    }

    if (restart && current_value != m_iStreamPosPollerInterval) {
        if (KillTimer(TIMER_STREAMPOSPOLLER)) {
            SetTimer(TIMER_STREAMPOSPOLLER, m_iStreamPosPollerInterval, nullptr);
        }
    }
}

void CMainFrame::SetTimersPlay()
{
    AdjustStreamPosPoller(false);

    SetTimer(TIMER_STREAMPOSPOLLER, m_iStreamPosPollerInterval, nullptr);
    SetTimer(TIMER_STREAMPOSPOLLER2, 500, nullptr);
    SetTimer(TIMER_STATS, 1000, nullptr);
}

void CMainFrame::KillTimerDelayedSeek()
{
    KillTimer(TIMER_DELAYEDSEEK);
    queuedSeek = { 0, 0, false };
}

void CMainFrame::KillTimersStop()
{
    KillTimerDelayedSeek();
    KillTimer(TIMER_STREAMPOSPOLLER2);
    KillTimer(TIMER_STREAMPOSPOLLER);
    KillTimer(TIMER_STATS);
    m_timerOneTime.Unsubscribe(TimerOneTimeSubscriber::DVBINFO_UPDATE);

    MSG msg;
    int pm = 0;
    while ((pm++ < 5) && PeekMessage(&msg, nullptr, WM_TIMER, WM_TIMER, PM_REMOVE)) {
        if (msg.wParam == TIMER_STREAMPOSPOLLER || msg.wParam == TIMER_STREAMPOSPOLLER2 || msg.wParam == TIMER_STATS || msg.wParam == TIMER_DELAYEDSEEK) {
            TRACE(L"Purged WM_TIMER during stop, wParam=%llu\n", msg.wParam);
        } else {
            DispatchMessage(&msg);
        }
    }
}

void CMainFrame::OnPlaySeekKey(UINT nID)
{
    if (!m_kfs.empty()) {
        bool bSeekingForward = (nID == ID_PLAY_SEEKKEYFORWARD);
        const REFERENCE_TIME rtPos = m_wndSeekBar.GetPos();
        REFERENCE_TIME rtKeyframe;
        REFERENCE_TIME rtTarget;
        REFERENCE_TIME rtMin;
        REFERENCE_TIME rtMax;
        if (bSeekingForward) {
            rtMin = rtPos + 10000LL; // at least one millisecond later
            rtMax = GetDur();
            rtTarget = rtMin;
        } else {
            rtMin = 0;
            if (GetMediaState() == State_Paused) {
                rtMax = rtPos - 10000LL;
            } else {
                rtMax = rtPos - 5000000LL;
            }
            rtTarget = rtMax;
        }

        if (GetKeyFrame(rtTarget, rtMin, rtMax, false, rtKeyframe)) {
            SeekTo(rtKeyframe);
        }
    }
}

void CMainFrame::OnUpdatePlaySeek(CCmdUI* pCmdUI)
{
    bool fEnable = false;

    if (GetLoadState() == MLS::LOADED) {
        fEnable = true;
        if (GetPlaybackMode() == PM_DVD && m_iDVDDomain != DVD_DOMAIN_Title) {
            fEnable = false;
        } else if (IsPlaybackCaptureMode()) {
            fEnable = false;
        }
    }

    pCmdUI->Enable(fEnable);
}

void CMainFrame::SetPlayingRate(double rate)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }
    HRESULT hr = E_FAIL;
    if (GetPlaybackMode() == PM_FILE) {
        if (GetMediaState() != State_Running) {
            SendMessage(WM_COMMAND, ID_PLAY_PLAY);
        }
        if (m_pMS) {
            hr = m_pMS->SetRate(rate);
        }
    } else if (GetPlaybackMode() == PM_DVD) {
        if (GetMediaState() != State_Running) {
            SendMessage(WM_COMMAND, ID_PLAY_PLAY);
        }
        if (rate > 0) {
            hr = m_pDVDC->PlayForwards(rate, DVD_CMD_FLAG_Block, nullptr);
        } else {
            hr = m_pDVDC->PlayBackwards(-rate, DVD_CMD_FLAG_Block, nullptr);
        }
    }
    if (SUCCEEDED(hr)) {
        m_dSpeedRate = rate;
        CString strODSMessage;
        strODSMessage.Format(IDS_OSD_SPEED, rate);
        m_OSD.DisplayMessage(OSD_TOPRIGHT, strODSMessage);
        m_media_trans_control.SetPlaybackRate(rate);
        MediaTransportControlUpdateTimeline(true);
    }
}

void CMainFrame::OnPlayChangeRate(UINT nID)
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    if (GetPlaybackMode() == PM_FILE) {
        const CAppSettings& s = AfxGetAppSettings();
        double dSpeedStep = s.nSpeedStep / 100.0;

        if (nID == ID_PLAY_INCRATE) {
            if (s.nSpeedStep > 0) {
                if (m_dSpeedRate <= 0.05) {
                    double newrate = 1.0 - (95 / s.nSpeedStep) * dSpeedStep;
                    SetPlayingRate(newrate > 0.05 ? newrate : newrate + dSpeedStep);
                } else {
                    SetPlayingRate(std::max(0.05, m_dSpeedRate + dSpeedStep));
                }
            } else {
                SetPlayingRate(std::max(0.0625, m_dSpeedRate * 2.0));
            }
        } else if (nID == ID_PLAY_DECRATE) {
            if (s.nSpeedStep > 0) {
                SetPlayingRate(std::max(0.05, m_dSpeedRate - dSpeedStep));
            } else {
                SetPlayingRate(std::max(0.0625, m_dSpeedRate / 2.0));
            }
        } else if (nID > ID_PLAY_PLAYBACKRATE_START && nID < ID_PLAY_PLAYBACKRATE_END) {
            if (filePlaybackRates.count(nID) != 0) {
                SetPlayingRate(filePlaybackRates[nID]);
            } else if (nID >= ID_PLAY_PLAYBACKRATE_FPS23 || nID <= ID_PLAY_PLAYBACKRATE_FPS59) {
                if (m_pCAP) {
                    float target = 25.0f;
                    if (nID == ID_PLAY_PLAYBACKRATE_FPS24) target = 24.0f;
                    else if (nID == ID_PLAY_PLAYBACKRATE_FPS23) target = 23.976f;
                    else if (nID == ID_PLAY_PLAYBACKRATE_FPS59) target = 59.94f;
                    SetPlayingRate(target / m_pCAP->GetFPS());
                }
            }
        }
    } else if (GetPlaybackMode() == PM_DVD) {
        if (nID == ID_PLAY_INCRATE) {
            if (m_dSpeedRate > 0) {
                SetPlayingRate(m_dSpeedRate * 2.0);
            } else if (m_dSpeedRate >= -1) {
                SetPlayingRate(1);
            } else {
                SetPlayingRate(m_dSpeedRate / 2.0);
            }
        } else if (nID == ID_PLAY_DECRATE) {
            if (m_dSpeedRate < 0) {
                SetPlayingRate(m_dSpeedRate * 2.0);
            } else if (m_dSpeedRate <= 1) {
                SetPlayingRate(-1);
            } else {
                SetPlayingRate(m_dSpeedRate / 2.0);
            }
        } else if (nID > ID_PLAY_PLAYBACKRATE_START && nID < ID_PLAY_PLAYBACKRATE_END) {
            if (dvdPlaybackRates.count(nID) != 0) {
                SetPlayingRate(dvdPlaybackRates[nID]);
            }
        }
    } else if (GetPlaybackMode() == PM_ANALOG_CAPTURE) {
        if (GetMediaState() != State_Running) {
            SendMessage(WM_COMMAND, ID_PLAY_PLAY);
        }

        long lChannelMin = 0, lChannelMax = 0;
        m_pAMTuner->ChannelMinMax(&lChannelMin, &lChannelMax);
        long lChannel = 0, lVivSub = 0, lAudSub = 0;
        m_pAMTuner->get_Channel(&lChannel, &lVivSub, &lAudSub);

        long lFreqOrg = 0, lFreqNew = -1;
        m_pAMTuner->get_VideoFrequency(&lFreqOrg);

        //long lSignalStrength;
        do {
            if (nID == ID_PLAY_DECRATE) {
                lChannel--;
            } else if (nID == ID_PLAY_INCRATE) {
                lChannel++;
            }

            //if (lChannel < lChannelMin) lChannel = lChannelMax;
            //if (lChannel > lChannelMax) lChannel = lChannelMin;

            if (lChannel < lChannelMin || lChannel > lChannelMax) {
                break;
            }

            if (FAILED(m_pAMTuner->put_Channel(lChannel, AMTUNER_SUBCHAN_DEFAULT, AMTUNER_SUBCHAN_DEFAULT))) {
                break;
            }

            long flFoundSignal;
            m_pAMTuner->AutoTune(lChannel, &flFoundSignal);

            m_pAMTuner->get_VideoFrequency(&lFreqNew);
        } while (FALSE);
        /*SUCCEEDED(m_pAMTuner->SignalPresent(&lSignalStrength))
        && (lSignalStrength != AMTUNER_SIGNALPRESENT || lFreqNew == lFreqOrg));*/
    } else {
        ASSERT(FALSE);
    }
}

void CMainFrame::OnUpdatePlayChangeRate(CCmdUI* pCmdUI)
{
    bool fEnable = false;

    if (GetLoadState() == MLS::LOADED) {
        if (pCmdUI->m_nID > ID_PLAY_PLAYBACKRATE_START && pCmdUI->m_nID < ID_PLAY_PLAYBACKRATE_END && pCmdUI->m_pMenu) {
            fEnable = false;
            if (GetPlaybackMode() == PM_FILE) {
                if (filePlaybackRates.count(pCmdUI->m_nID) != 0) {
                    fEnable = true;
                    if (filePlaybackRates[pCmdUI->m_nID] == m_dSpeedRate) {
                        pCmdUI->m_pMenu->CheckMenuRadioItem(ID_PLAY_PLAYBACKRATE_START, ID_PLAY_PLAYBACKRATE_END, pCmdUI->m_nID, MF_BYCOMMAND);
                    }
                } else if (pCmdUI->m_nID >= ID_PLAY_PLAYBACKRATE_FPS23 || pCmdUI->m_nID <= ID_PLAY_PLAYBACKRATE_FPS59) {
                    fEnable = true;
                    if (m_pCAP) {
                        float target = 25.0f;
                        if (pCmdUI->m_nID == ID_PLAY_PLAYBACKRATE_FPS24) target = 24.0f;
                        else if (pCmdUI->m_nID == ID_PLAY_PLAYBACKRATE_FPS23) target = 23.976f;
                        else if (pCmdUI->m_nID == ID_PLAY_PLAYBACKRATE_FPS59) target = 59.94f;
                        if (target / m_pCAP->GetFPS() == m_dSpeedRate) {
                            bool found = false;
                            for (auto const& [key, rate] : filePlaybackRates) { //make sure it wasn't a standard rate already
                                if (rate == m_dSpeedRate) {
                                    found = true;
                                }
                            }
                            if (!found) { //must have used fps, as it didn't match a standard rate
                                pCmdUI->m_pMenu->CheckMenuRadioItem(ID_PLAY_PLAYBACKRATE_START, ID_PLAY_PLAYBACKRATE_END, pCmdUI->m_nID, MF_BYCOMMAND);
                            }
                        }
                    }
                }
            } else if (GetPlaybackMode() == PM_DVD) {
                if (dvdPlaybackRates.count(pCmdUI->m_nID) != 0) {
                    fEnable = true;
                    if (dvdPlaybackRates[pCmdUI->m_nID] == m_dSpeedRate) {
                        pCmdUI->m_pMenu->CheckMenuRadioItem(ID_PLAY_PLAYBACKRATE_START, ID_PLAY_PLAYBACKRATE_END, pCmdUI->m_nID, MF_BYCOMMAND);
                    }
                }
            }
        } else {
            bool fInc = pCmdUI->m_nID == ID_PLAY_INCRATE;

            fEnable = true;
            if (fInc && m_dSpeedRate >= 128.0) {
                fEnable = false;
            } else if (!fInc && GetPlaybackMode() == PM_FILE && m_dSpeedRate <= 0.05) {
                fEnable = false;
            } else if (!fInc && GetPlaybackMode() == PM_DVD && m_dSpeedRate <= -128.0) {
                fEnable = false;
            } else if (GetPlaybackMode() == PM_DVD && m_iDVDDomain != DVD_DOMAIN_Title) {
                fEnable = false;
            } else if (m_fShockwaveGraph) {
                fEnable = false;
            } else if (GetPlaybackMode() == PM_ANALOG_CAPTURE && (!m_wndCaptureBar.m_capdlg.IsTunerActive() || m_fCapturing)) {
                fEnable = false;
            } else if (GetPlaybackMode() == PM_DIGITAL_CAPTURE) {
                fEnable = false;
            } else if (m_fLiveWM) {
                fEnable = false;
            }
        }
    }

    pCmdUI->Enable(fEnable);
}

void CMainFrame::OnPlayResetRate()
{
    if (GetLoadState() != MLS::LOADED) {
        return;
    }

    HRESULT hr = E_FAIL;

    if (GetMediaState() != State_Running) {
        SendMessage(WM_COMMAND, ID_PLAY_PLAY);
    }

    if (GetPlaybackMode() == PM_FILE) {
        hr = m_pMS->SetRate(1.0);
    } else if (GetPlaybackMode() == PM_DVD) {
        hr = m_pDVDC->PlayForwards(1.0, DVD_CMD_FLAG_Block, nullptr);
    }

    if (SUCCEEDED(hr)) {
        m_dSpeedRate = 1.0;

        CString strODSMessage;
        strODSMessage.Format(IDS_OSD_SPEED, m_dSpeedRate);
        m_OSD.DisplayMessage(OSD_TOPRIGHT, strODSMessage);
        m_media_trans_control.SetPlaybackRate(m_dSpeedRate);
        MediaTransportControlUpdateTimeline(true);
    }
}

void CMainFrame::OnUpdatePlayResetRate(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(GetLoadState() == MLS::LOADED);
}

void CMainFrame::SetAudioDelay(REFERENCE_TIME rtShift)
{
    if (CComQIPtr<IAudioSwitcherFilter> pASF = FindFilter(__uuidof(CAudioSwitcherFilter), m_pGB)) {
        pASF->SetAudioTimeShift(rtShift);

        if (GetLoadState() == MLS::LOADED) {
            CString str;
            str.Format(IDS_MAINFRM_70, rtShift / 10000);
            SendStatusMessage(str, 3000);
            m_OSD.DisplayMessage(OSD_TOPLEFT, str);
        }
    }
}

void CMainFrame::SetSubtitleDelay(int delay_ms, bool relative)
{
    if (!m_pCAP && !m_pDVS) {
        if (GetLoadState() == MLS::LOADED) {
            SendStatusMessage(L"Delay is not supported by current subtitle renderer", 3000, true);
        }
        return;
    }

    ResetAutoCopySubtitle(); // the new delay moves the segment boundaries

    if (m_pDVS) {
        int currentDelay, speedMul, speedDiv;
        if (FAILED(m_pDVS->get_SubtitleTiming(&currentDelay, &speedMul, &speedDiv))) {
            return;
        }
        if (relative) {
            delay_ms += currentDelay;
        }

        VERIFY(SUCCEEDED(m_pDVS->put_SubtitleTiming(delay_ms, speedMul, speedDiv)));
    }
    else {
        ASSERT(m_pCAP != nullptr);
        if (m_pSubStreams.IsEmpty()) {
            SendStatusMessage(StrRes(IDS_SUBTITLES_ERROR), 3000, true);
            return;
        }
        if (relative) {
            delay_ms += m_pCAP->GetSubtitleDelay();
        }

        m_pCAP->SetSubtitleDelay(delay_ms);
    }

    CString strSubDelay;
    strSubDelay.Format(IDS_MAINFRM_139, delay_ms);
    SendStatusMessage(strSubDelay, 3000);
    m_OSD.DisplayMessage(OSD_TOPLEFT, strSubDelay);
}

void CMainFrame::OnPlayChangeAudDelay(UINT nID)
{
    if (CComQIPtr<IAudioSwitcherFilter> pASF = FindFilter(__uuidof(CAudioSwitcherFilter), m_pGB)) {
        REFERENCE_TIME rtShift = pASF->GetAudioTimeShift();
        rtShift +=
            nID == ID_PLAY_INCAUDDELAY ? 100000 :
            nID == ID_PLAY_DECAUDDELAY ? -100000 :
            0;

        SetAudioDelay(rtShift);
    }
}

void CMainFrame::OnUpdatePlayChangeAudDelay(CCmdUI* pCmdUI)
{
    pCmdUI->Enable(!!m_pGB /*&& !!FindFilter(__uuidof(CAudioSwitcherFilter), m_pGB)*/);
}

void CMainFrame::OnPlayFiltersCopyToClipboard()
{
    // Don't translate that output since it's mostly for debugging purpose
    CString filtersList = _T("Filters currently loaded:\r\n");
    // Skip the first two entries since they are the "Copy to clipboard" menu entry and a separator
    for (int i = 2, count = m_filtersMenu.GetMenuItemCount(); i < count; i++) {
        CString filterName;
        m_filtersMenu.GetMenuString(i, filterName, MF_BYPOSITION);
        filterName.Replace(_T("&&"), _T("&")); //the label is escaped for the menu, this list is plain text
        filtersList.AppendFormat(_T("  - %s\r\n"), filterName.GetString());
    }

    CClipboard clipboard(this);
    VERIFY(clipboard.SetText(filtersList));
}

bool CMainFrame::FilterSettingsByClassID(CLSID clsid, CWnd* parent)
{
    for (int a = 0; a < m_pparray.GetCount(); a++) {
        CComQIPtr<IBaseFilter> pBF2 = m_pparray[a];
        if (pBF2) {
            CLSID tclsid;
            pBF2->GetClassID(&tclsid);
            if (tclsid == clsid) {
                FilterSettings(m_pparray[a], parent);
                return true;
            }
        }
    }
    return false;
}

void CMainFrame::FilterSettings(CComPtr<IUnknown> pUnk, CWnd* parent) {
    CComPropertySheet ps(IDS_PROPSHEET_PROPERTIES);

    CComQIPtr<IBaseFilter> pBF = pUnk;
    CLSID clsid = GetCLSID(pBF);
    CFGFilterLAV::LAVFILTER_TYPE LAVFilterType = CFGFilterLAV::INVALID;
    bool bIsInternalLAV = CFGFilterLAV::IsInternalInstance(pBF, &LAVFilterType);

    if (CComQIPtr<ISpecifyPropertyPages> pSPP = pUnk) {
        ULONG uIgnoredPage = ULONG(-1);
        // If we are dealing with an internal filter, we want to ignore the "Formats" page.
        if (bIsInternalLAV) {
            uIgnoredPage = (LAVFilterType != CFGFilterLAV::AUDIO_DECODER) ? 1 : 2;
        }
        bool bIsInternalFilter = bIsInternalLAV || clsid == CLSID_MPCVR;
        ps.AddPages(pSPP, bIsInternalFilter, uIgnoredPage);
    }

    HRESULT hr;
    CComPtr<IPropertyPage> pPP = DEBUG_NEW CInternalPropertyPageTempl<CPinInfoWnd>(nullptr, &hr);
    ps.AddPage(pPP, pBF);

    if (ps.GetPageCount() > 0) {
        CMPCThemeComPropertyPage::SetDialogType(clsid);
        ps.DoModal();

        if (bIsInternalLAV) {
            if (CComQIPtr<ILAVFSettings> pLAVFSettings = pBF) {
                CFGFil×¾ûó†òµë(š+myÔEdB†GfGF‚ÂÕ÷f–FVõvæBÓæÕö…væBÂfÇ6R“°Ð¢6–bÐ¢òò&Wf–WrFöW2æ÷BÇv—2v÷&²vööBv—F‚EdBWfVâv†VâÆöFVBg&öÒ†F@Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢6VÇ6PÐ¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢–b‚F„—4öä÷F–6ÄF—62†GfGF‚’’°Ð¢Õ÷t%÷&Wf–WrÒDT%TuôäUr4dtÖævW$EdB†GfGF‚ÂÕ÷væE&Uf–WrävWEf–FVô…täB‚’ÂG'VR“°Ð¢ÒVÇ6R°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ¢ÐÐ¢6VæF–`Ð¢ÒVÇ6R–b†WFò÷VäFWf–6TFFÒG–æÖ–5ö67CÄ÷VäFWf–6TFF£â‡ôÔB’’°Ð¢–b‡2æ”FVfVÇD6GW&TFWf–6RÓÒ’°Ð¢Õ÷t"ÒDT%TuôäUr4dtÖævW$$D†Õ÷f–FVõvæBÓæÕö…væB“°Ð¢ÒVÇ6R°Ð¢Õ÷t"ÒDT%TuôäUr4dtÖævW$6GW&R†Õ÷f–FVõvæBÓæÕö…væB“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚Õ÷t"’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õóƒ°Ð¢ÐÐ Ð¢–b‚Õ÷t%÷&Wf–Wr’°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ Ð¢Õ÷t"ÓäFEFõ$õB‚“°Ð Ð¢Õ÷Ô2ÒÕ÷t#°Ð¢Õ÷ÔRÒÕ÷t#°Ð¢Õ÷Õ2ÒÕ÷t#²òòvVæW&ÀÐ¢Õ÷erÒÕ÷t#°Ð¢Õ÷%bÒÕ÷t#²òòf–FVðÐ¢Õ÷$ÒÕ÷t#²òòVF–ðÐ¢Õ÷e2ÒÕ÷t#°Ð Ð¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢Õ÷t%÷&Wf–WrÓäFEFõ$õB‚“°Ð Ð¢Õ÷Ô5÷&Wf–WrÒÕ÷t%÷&Wf–Ws°Ð¢òöÕ÷ÔU÷&Wf–WrÒÕ÷t%÷&Wf–Ws°Ð¢Õ÷Õ5÷&Wf–WrÒÕ÷t%÷&Wf–Ws²òòvVæW&ÀÐ¢Õ÷eu÷&Wf–WrÒÕ÷t%÷&Wf–Ws°Ð¢Õ÷%e÷&Wf–WrÒÕ÷t%÷&Wf–Ws°Ð¢òöÕ÷e5÷&Wf–WrÒÕ÷t%÷&Wf–Ws°Ð¢ÐÐ Ð¢–b‚†Õ÷Ô2bbÕ÷ÔRbbÕ÷Õ2’ÇÂ†Õ÷erbbÕ÷%b’ÇÂ†Õ÷$’’°Ð¢F‡&÷r…T”åB””E5ôu$…ô”åDU$d4U5ôU%$õ#°Ð¢ÐÐ Ð¢–b„d”ÄTB†Õ÷ÔRÓå6WDæ÷F–g•v–æF÷r‚„ô…täB–Õö…væBÂtÕôu$„äõD”e’Â„Å$Ò–Õ÷ÔRç’’’°Ð¢F‡&÷r…T”åB””E5ôu$…õD$tUEõtäEôU%$õ#°Ð¢ÐÐ Ð¢Õ÷&÷bÒ„•Væ¶æ÷vâ¢”DT%TuôäUr4¶W•&÷f–FW"‚“°Ð Ð¢–b„46öÕ•G#Ä”ö&¦V7Ev—F…6—FSâö&¦V7Ev—F…6—FRÒÕ÷t"’°Ð¢ö&¦V7Ev—F…6—FRÓå6WE6—FR†Õ÷&÷b“°Ð¢ÐÐ Ð¢Õ÷4"ÒDT%TuôäUr4E4Ô6†FW$&r†çVÆÇG"ÂçVÆÇG"“°Ð§ÐÐ Ð¤5væB¢4Ö–äg&ÖS£¤vWDÖöFÅ&VçB‚Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢5væB¢&VçEvæBÒF†—3°Ð¢–b„†4FVF–6FVDe5f–FVõv–æF÷r‚’bb2æÕõ&VæFW&W'56WGF–æw2æÕôGe&VæE6WG2æ%dÕ#”gVÆÇ67&VVäuT•7W÷'B’°Ð¢&VçEvæBÒÕ÷FVF–6FVDe5f–FVõvæC°Ð¢ÐÐ¢&WGW&â&VçEvæC°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6†÷tÖVF–G—W4F–Æör‚’°Ð¢–b‚Õöd÷Væ–æt&÷'FVB’°Ð¢4WFôÆö6²Æ6²‚fÆö6´ÖöFÄF–Æör“°Ð¢46öÕ•G#Ä”w&„'V–ÆFW$FVDVæCât$DRÒÕ÷t#°Ð¢–b‡t$DRbbt$DRÓävWD6÷VçB‚’’°Ð¢ÖVF–G—W4W'&÷$FÆrÒDT%TuôäUr4ÖVF–G—W4FÆr‡t$DRÂvWDÖöFÅ&VçB‚’“°Ð¢ÖVF–G—W4W'&÷$FÆrÓäFôÖöFÂ‚“°Ð¢FVÆWFRÖVF–G—W4W'&÷$FÆs°Ð¢ÖVF–G—W4W'&÷$FÆrÒçVÆÇG#°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&VÆV6U&Wf–Wtw&‚‚Ð§°Ð¢–b†Õ÷t%÷&Wf–Wr’°Ð¢Õ÷4%÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷Ôee÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷ÔedD5÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷dÕ#”5÷&Wf–Wrå&VÆV6R‚“°Ð Ð¢òöÕ÷e5÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷Õ5÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷%e÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷eu÷&Wf–Wrå&VÆV6R‚“°Ð¢òöÕ÷ÔU÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷Ô5÷&Wf–Wrå&VÆV6R‚“°Ð Ð¢–b†Õ÷EdD5÷&Wf–Wr’°Ð¢Õ÷EdD5÷&Wf–Wrå&VÆV6R‚“°Ð¢Õ÷EdD•÷&Wf–Wrå&VÆV6R‚“°Ð¢ÐÐ Ð¢Õ÷t%÷&Wf–WrÓå&VÖ÷fTg&öÕ$õB‚“°Ð¢Õ÷t%÷&Wf–Wrå&VÆV6R‚“°Ð¢ÐÐ§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥&Wf–Wuv–æF÷t†–FR‚’°Ð¢…$U5TÅB‡"Ò5ôô³°Ð Ð¢–b‚Õö%W6U6VVµ&Wf–Wr’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢–b†Õ÷væE&Uf–Wrä—5v–æF÷uf—6–&ÆR‚’’°Ð¢òòF—6&ÆRæ–ÖF–öàÐ¢ä”ÔD”ôä”ädòæ–ÖF–öä–æfó°Ð¢æ–ÖF–öä–æfòæ6%6—¦RÒ6—¦Vöb„ä”ÔD”ôä”ädò“°Ð¢£¥7—7FVÕ&ÖWFW'4–æfò…5•ôtUDä”ÔD”ôâÂ6—¦Vöb„ä”ÔD”ôä”ädò’Âdæ–ÖF–öä–æfòÂ“°Ð¢–çBv–æF÷tæ–ÖF–öåG—RÒæ–ÖF–öä–æfòæ”Ö–äæ–ÖFS°Ð¢æ–ÖF–öä–æfòæ”Ö–äæ–ÖFRÒ°Ð¢£¥7—7FVÕ&ÖWFW'4–æfò…5•õ4UDä”ÔD”ôâÂ6—¦Vöb„ä”ÔD”ôä”ädò’Âdæ–ÖF–öä–æfòÂ“°Ð Ð¢Õ÷væE&Uf–Wrå6†÷uv–æF÷r…5uô„”DR“°Ð Ð¢òòVæ&ÆRæ–ÖF–öàÐ¢æ–ÖF–öä–æfòæ”Ö–äæ–ÖFRÒv–æF÷tæ–ÖF–öåG—S°Ð¢£¥7—7FVÕ&ÖWFW'4–æfò…5•õ4UDä”ÔD”ôâÂ6—¦Vöb„ä”ÔD”ôä”ädò’Âdæ–ÖF–öä–æfòÂ“°Ð Ð¢–b†Õ÷t%÷&Wf–WrbbÕ÷Ô5÷&Wf–Wr’°Ð¢Õ÷Ô5÷&Wf–WrÓåW6R‚“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&â‡#°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥&Wf–Wuv–æF÷u6†÷r…$TdU$Tä4UõD”ÔR'D7W#"’°Ð¢–b‚6å&Wf–WuW6R‚’’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢…$U5TÅB‡"Ò5ôô³°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBbbÕ÷EdD5÷&Wf–Wr’°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö2ÂÆö3#°Ð¢F÷V&ÆRg2Ò°Ð Ð¢‡"ÒÕ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚dÆö2“°Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢‡"ÒÕ÷EdD•÷&Wf–WrÓävWD7W'&VçDÆö6F–öâ‚dÆö3"“°Ð Ð¢g2ÒÆö2åF–ÖT6öFTfÆw2ÓÒEdEõD5ôdÄuó#Vg2ò#Rã Ð¢¢Æö2åF–ÖT6öFTfÆw2ÓÒEdEõD5ôdÄuó3g2ò3ã Ð¢¢Æö2åF–ÖT6öFTfÆw2ÓÒEdEõD5ôdÄuôG&÷g&ÖRò#’ã“pÐ¢¢#Rã°Ð Ð¢EdEô„Õ4eõD”ÔT4ôDRGfEFòÒ%C$„Õ4b‡'D7W#"Âg2“°Ð Ð¢–b„d”ÄTB†‡"’ÇÂ„Æö2åF—FÆTçVÒÒÆö3"åF—FÆTçVÒ’’°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ•F—FÆR„Æö2åF—FÆTçVÒÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ¢Õ÷EdD5÷&Wf–WrÓå&W7VÖR„EdEô4ÔEôdÄuô&Æö6²ÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b…5T44TTDTB†‡"’’°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ”EF–ÖR‚fGfEFòÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ¢ÒVÇ6R°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ”6†FW$–åF—FÆR„Æö2åF—FÆTçVÒÂÂEdEô4ÔEôdÄuô&Æö6²ÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ”EF–ÖR‚fGfEFòÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b„d”ÄTB†‡"’’°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ”EF–ÖT–åF—FÆR„Æö2åF—FÆTçVÒÂfGfEFòÂEdEô4ÔEôdÄuô&Æö6²ÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢‡"ÒÕ÷EdD5÷&Wf–WrÓåÆ”EF–ÖR‚fGfEFòÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ¢ÐÐ Ð¢Õ÷EdD•÷&Wf–WrÓävWD7W'&VçDÆö6F–öâ‚dÆö3"“°Ð Ð¢Õ÷Ô5÷&Wf–WrÓå'Vâ‚“°Ð¢6ÆVWƒ“°Ð¢Õ÷Ô5÷&Wf–WrÓåW6R‚“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRbbÕ÷Õ5÷&Wf–Wr’°Ð¢‡"ÒÕ÷Õ5÷&Wf–WrÓå6WE÷6—F–öç2‚g'D7W#"ÂÕõ4TT´”äuô'6öÇWFU÷6—F–öæ–ærÂçVÆÇG"ÂÕõ4TT´”äuôæõ÷6—F–öæ–ær“°Ð¢ÒVÇ6R°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢–b„d”ÄTB†‡"’’°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢ò Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢‡"Òe3"òe3"Óå7FWƒ"ÂçVÆÇG"’¢Uôd”Ã°Ð¢–b…5T44TTDTB†‡"’’°Ð¢6ÆVWƒ“°Ð¢ÐÐ¢ÐÐ¢¢ðÐ Ð¢–b‚Õ÷væE&Uf–Wrä—5v–æF÷uf—6–&ÆR‚’’°Ð¢Õ÷væE&Uf–Wrå6WE&VÆF—fU6—¦R„g„vWD6WGF–æw2‚’æ•6VVµ&Wf–Wu6—¦R“°Ð¢Õ÷væE&Uf–Wrå6†÷uv–æF÷r…5uõ4„õtäô5D•dDR“°Ð¢–b„vWDW…7G–ÆR‚’bu5ôU…õDõÔõ5B’°Ð¢òòF†R&Wf–Wr—2â÷væVB÷WÂ6ò—B6†÷VÆBÇ&VG’föÆÆ÷rF†RÖ–âv–æF÷r–çFòF†PÐ¢òòF÷Ö÷7B&æBâ—B†2&VVâ&W÷'FVB&V†–æBâÇv—2Ööâ×F÷Ö–âv–æF÷r‚33ƒC’’Â6ðÐ¢òòWB—B–âF†B&æBW‡Æ–6—FÇ’26fVwV&Bâæ÷F†–ærFòFòv†Vâæ÷BF÷Ö÷7C Ð¢òòv–æF÷w2Ö÷fW2÷væVBv–æF÷w2÷WBöbF†RF÷Ö÷7B&æBÆöærv—F‚F†V—"÷væW"àÐ¢Õ÷væE&Uf–Wrå6WEv–æF÷u÷2‚gvæEF÷Ö÷7BÂÂÂÂÂ5uôäôÔõdRÂ5uôäõ4•¤RÂ5uôäô5D•dDR“°Ð¢ÐÐ¢Õ÷væE&Uf–Wrå6WEv–æF÷u6—¦R‚“°Ð¢ÐÐ Ð¢&WGW&â‡#°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7–æ5&Wf–WtVF—F–öâ‚Ð§°Ð¢òòÄb7Æ—GFW"W‡÷6W2ÖG&÷6¶VF—F–öç2F‡&÷Vv‚”Õ7G&VÕ6VÆV7Bv—F‚w&÷W‚àÐ¢òòF†R&Wf–Wrw&‚—2æ÷Bv&RöbVF—F–öâ6†ævW2ÖFR–âF†RÖ–âw&‚ÀÐ¢òò6ò6VÆV7BF†R6ÖRVF—F–öâF†W&RFò¶VWF†R&Wf–WvVBF–ÖVÆ–æR–â7–æ2àÐ¢–b‚Õ÷t%÷&Wf–WrÇÂÕ÷7Æ—GFW%52’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB†Õ÷7Æ—GFW%52Óä6÷VçB‚f57G&V×2’’ÇÂ57G&V×2Â2’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–çB6VÆV7FVDVF—F–öâÒÓ°Ð¢–çBVF—F–öä6÷VçBÒ°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW%52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’bbGtw&÷WÓÒ‚’°Ð¢–b†GtfÆw2’°Ð¢6VÆV7FVDVF—F–öâÒVF—F–öä6÷VçC°Ð¢ÐÐ¢VF—F–öä6÷VçB²³°Ð¢ÐÐ¢ÐÐ¢–b†VF—F–öä6÷VçBÂ"ÇÂ6VÆV7FVDVF—F–öâÂ’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t%÷&Wf–WrÂTbÂ$b’°Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ52Ò$b’°Ð¢–b„d”ÄTB‡52Óä6÷VçB‚f57G&V×2’’ÇÂ57G&V×2ÂVF—F–öä6÷VçB²’°Ð¢6öçF–çVS°Ð¢ÐÐ¢–çBVF—F–öâÒ°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢–b…5T44TTDTB‡52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’bbGtw&÷WÓÒ‚’°Ð¢–b†VF—F–öâÓÒ6VÆV7FVDVF—F–öâ’°Ð¢–b‚GtfÆw2’°Ð¢52ÓäVæ&ÆR†’ÂÕ5E$TÕ4TÄT5DTä$ÄUôTä$ÄR“°Ð¢ÐÐ¢&WGW&ã°Ð¢ÐÐ¢VF—F–öâ²³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¤†æFÆT×VÇF—ÆTVçG'•&"„57G&–æurfâÂ–çB¢VçG'”–æFW‚’°Ð¢5$e4Æ—7BÄ5$e4f–ÆSâf–ÆUöÆ—7B‡G'VR“²ò÷G'VRÒ6ÆV'2—G6VÆböâFW7G'V7F–öàÐ¢–çBçVÕöf–ÆW2ÂçVÕööµöf–ÆW3°Ð Ð¢5$$f–ÆU6÷W&6S£¥66ä&6†—fR†fâävWD'VffW"‚’Âff–ÆUöÆ—7BÂfçVÕöf–ÆW2ÂfçVÕööµöf–ÆW2“°Ð¢–b†çVÕööµöf–ÆW2â’°Ð¢57G&–æurVçG'”æÖS°Ð Ð¢–b‡VçG'”–æFW‚bb§VçG'”–æFW‚ãÒ’°Ð¢òòW6RF†R&÷f–FVB–æFW€Ð¢5$e4f–ÆR¢f–ÆRÒf–ÆUöÆ—7Bäf—'7B‚“°Ð¢f÷"†–çB’Ò²’Â§VçG'”–æFW‚bbf–ÆS²’²²’°Ð¢f–ÆRÒf–ÆUöÆ—7BäæW‡B†f–ÆR“°Ð¢ÐÐ¢–b†f–ÆR’°Ð¢VçG'”æÖRÒf–ÆRÓæf–ÆVæÖS°Ð¢ÐÐ¢ÒVÇ6R°Ð¢òò6†÷rF–ÆörFò6VÆV7BVçG'Ð¢&$VçG'•6VÆV7F÷$F–ÆörVçG'•6VÆV7F÷"‚ff–ÆUöÆ—7BÂvWDÖöFÅ&VçB‚’“°Ð¢–b„”Dô²ÓÒVçG'•6VÆV7F÷"äFôÖöFÂ‚’’°Ð¢VçG'”æÖRÒVçG'•6VÆV7F÷"ävWD7W'&VçDVçG'’‚“°Ð¢–b‡VçG'”–æFW‚’°Ð¢§VçG'”–æFW‚ÒVçG'•6VÆV7F÷"ävWD7W'&VçD–æFW‚‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†VçG'”æÖRävWDÆVæwF‚‚’â’°Ð¢46öÕG#Ä4dtÖævW#âfvÒÒ7FF–5ö67CÄ4dtÖævW"£â†Õ÷t"ç“°Ð¢&WGW&âfvÒÓå&VæFW%$e4f–ÆTVçG'’†fâÂçVÆÇG"ÂVçG'”æÖR“°Ð¢ÐÐ¢&WGW&â$e5ôUô$õ%C²ò÷vRf÷VæB×VÇF—ÆRVçG&–W2'WBæòVçG'’6VÆV7FVBàÐ¢ÐÐ¢&WGW&âUôäõD”ÕÃ²òöæ÷B×VÇF’ÖVçG'’& Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥G'•6¶—v—F†–å&"†&ööÂf÷'v&B’°Ð¢WFòf–ÆTFFÒG–æÖ–5ö67CÄ÷Väf–ÆTFF£â†ÕöÆ7DôÔBæÕ÷“°Ð¢–b‚f–ÆTFFÇÂf–ÆTFFÓç&$VçG'”–æFW‚Â’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢57G&–ærfâÒf–ÆTFFÓæfç2ävWD†VB‚“°Ð¢–b†fâä—4V×G’‚’’°Ð¢fâÒÆ7D÷Väf–ÆS°Ð¢ÐÐ Ð¢òò66âF†R$"&6†—fRFòvWBF†Rf–ÆRÆ—7@Ð¢5$e4Æ—7BÄ5$e4f–ÆSâf–ÆUöÆ—7B‡G'VR“°Ð¢–çBçVÕöf–ÆW2ÂçVÕööµöf–ÆW3°Ð¢5$$f–ÆU6÷W&6S£¥66ä&6†—fR†fâävWD'VffW"‚’Âff–ÆUöÆ—7BÂfçVÕöf–ÆW2ÂfçVÕööµöf–ÆW2“°Ð Ð¢–b†çVÕööµöf–ÆW2ÃÒ’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢òò6Æ7VÆFRæW‡B÷&Wf–÷W2VçG'’–æFW‚†æòw&&÷VæBÐ¢–çBæWt–æFWƒ°Ð¢–b†f÷'v&B’°Ð¢æWt–æFW‚Òf–ÆTFFÓç&$VçG'”–æFW‚²°Ð¢–b†æWt–æFW‚ãÒçVÕööµöf–ÆW2’°Ð¢&WGW&âfÇ6S²òòBF†RVæBÂ6¶—FòæW‡Bf–ÆPÐ¢ÐÐ¢ÒVÇ6R°Ð¢æWt–æFW‚Òf–ÆTFFÓç&$VçG'”–æFW‚Ò°Ð¢–b†æWt–æFW‚Â’°Ð¢&WGW&âfÇ6S²òòBF†R&Vv–ææ–ærÂ6¶—Fò&Wf–÷W2f–ÆPÐ¢ÐÐ¢ÐÐ Ð¢4WFõG#Ä÷Väf–ÆTFFâ„DT%TuôäUr÷Väf–ÆTFF‚’“°Ð¢Óæfç2äFD†VB†fâ“°Ð¢Óç&$VçG'”–æFW‚ÒæWt–æFWƒ°Ð¢÷VäÖVF–„4WFõG#Ä÷VäÖVF–FFâ‡äFWF6‚‚’’“°Ð¢&WGW&âG'VS°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Väf–ÆR„÷Väf–ÆTFF¢ôdBÐ§°Ð¢–b‡ôdBÓæfç2ä—4V×G’‚’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õóƒ°Ð¢ÐÐ Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢&ööÂ$Ö–äf–ÆRÒG'VS°Ð Ð¢õ4•D”ôâ÷2ÒôdBÓæfç2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢57G&–ærfâÒôdBÓæfç2ävWDæW‡B‡÷2“°Ð Ð¢fâåG&–Ò‚“°Ð¢–b†fâä—4V×G’‚’bb$Ö–äf–ÆR’°Ð¢'&V³°Ð¢ÐÐ¢–b†$Ö–äf–ÆR’°Ð¢–b†Õ÷'E&VÆöE÷2ãÒbbfâÒÕ÷&VÆöDf–ÆVæÖR’°Ð¢òò6ÆV"–æfòW6VBf÷"&VÆöF–æpÐ¢Õ÷'E&VÆöE÷2ÒÓ°Ð¢&VÆöD%&WVBÒ%&WVB‚“°Ð¢Õö•&VÆöDVF–ô–G‚ÒÓ°Ð¢Õö•&VÆöE7V$–G‚ÒÓ°Ð¢ÐÐ¢Õ÷&VÆöDf–ÆVæÖRäV×G’‚“°Ð Ð¢òò7F÷&R–æfòÂF†—2—2W6VBf÷"6¶—–ærFòæW‡B÷&Wf–÷W2f–ÆPÐ¢ôdBÓçF—FÆRÒfã°Ð¢Æ7D÷Väf–ÆRÒfã°Ð¢ÐÐ Ð¢57G&–ærW‡BÒvWDf–ÆTW‡B†fâ“°Ð¢–b†W‡BÓÒ"æ×Ç2"’°Ð¢57G&–ærfæâÒF…WF–Ç3£¥7G&—F„÷%W&Â†fâ“°Ð¢57G&–ærFV×F‚†fâ“°Ð¢FV×F‚å&WÆ6R†fæâÂõB‚""’“°Ð¢FV×F‚å&WÆ6R…õB‚$$DÕeÅÅÄ”Ä•5EÅÂ"’ÂõB‚""’“°Ð¢4†F×d6Æ—–æfò6Æ—–æfó°Ð¢Õö$†4$DÖWFÒ6Æ—–æfòå&VDÖWF‡FV×F‚ÂÕô$DÖWF“°Ð¢ÐÐ Ð¢…$U5TÅB‡#°Ð¢…$U5TÅB&$…"ÒUôäõD”ÕÃ°Ð¢6–b”åDU$äÅõ4õU$4Td”ÅDU%õ$e0Ð¢–b‡2å7&4f–ÇFW'5µ5$5õ$e5ÒbbF…WF–Ç3£¤—5U$Â†fâ’’°Ð¢57G&–ærW‡BÒ5F‚†fâ’ävWDW‡FVç6–öâ‚’äÖ¶TÆ÷vW"‚“°Ð¢–b†W‡BÓÒÂ"ç&""’°Ð¢&$…"Ò†æFÆT×VÇF—ÆTVçG'•&"†fâÂgôdBÓç&$VçG'”–æFW‚“°Ð¢ÐÐ¢ÐÐ¢6VæF–`Ð Ð¢–b„UôäõD”ÕÂÓÒ&$…"’°Ð¢‡"ÒÕ÷t"Óå&VæFW$f–ÆR†fâÂçVÆÇG"“°Ð¢ÒVÇ6R°Ð¢‡"Ò&$…#°Ð¢ÐÐ Ð¢–b„d”ÄTB†‡"’’°Ð¢–b†$Ö–äf–ÆR’°Ð¢–b†Õ÷ÔR’°Ð¢Õ÷ÔRÓå6WDæ÷F–g•v–æF÷r„åTÄÂÂÂ“°Ð¢ÐÐ Ð¢–b†‡"ÓÒdeuôUô4ääõEõ$TäDU"’°Ð¢46öÕG#Ä4dtÖævW#âfvÒÒ7FF–5ö67CÄ4dtÖævW"£â†Õ÷t"ç“°Ð¢–b†fvÒbbfvÒÓävWD–çFW&æÄf–ÇFW$ÆöF–æt&Æö6¶VB‚’’°Ð¢Etõ$B63°Ð¢–b„—5v–æF÷w5fW'6–öä÷$w&VFW$'V–ÆBƒÃÃ##’bb&VE&Vv—7G'”Etõ$B„„´U•ôÄô4ÅôÔ4„”äRÂÂ%5•5DTÕÅÄ7W'&VçD6öçG&öÅ6WEÅÄ6öçG&öÅÅÄ4•ÅÅ&÷FV7FVB"ÂÂ%fW&–f–VDæE&WWF&ÆUöÆ–7•7FFTÖ–åfÇVU6VVâ"Â62’bb‡62â’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õõ$TäDU$d”ÅôDÄÅõ43°Ð¢ÒVÇ6R°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õõ$TäDU$d”ÅôDÄÃ°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b‡2æe&W÷'Df–ÆVE–ç2bbÕöd÷Væ–æt&÷'FVB’°Ð¢46öÕ•G#Ä”w&„'V–ÆFW$FVDVæCât$DRÒÕ÷t#°Ð¢–b‡t$DRbbt$DRÓävWD6÷VçB‚’’°Ð¢&ööÂ6†÷v×FFÆrÒG'VS°Ð¢òòFöâwB6†÷rÖVæ–ævÆW72F–Æörv†Vâ—Bf–Ç2BvVæW&–26÷W&6Rf–ÇFW Ð¢–b†‡"ÓÒdeuôUô4ääõEõ$TäDU"bbt$DRÓävWD6÷VçB‚’ÓÒ’°Ð¢4FÄÆ—7CÄ57G&–æusâFƒ°Ð¢4FÄÆ—7CÄ4ÖVF–G—Sâ×G3°Ð¢–b…5ôô²ÓÒt$DRÓävWDFVDVæBƒÂF‚Â×G2’bbF‚ävWD6÷VçB‚’ÓÒ’°Ð¢–b‡F‚ävWD†VB‚’ÓÒÂ$f–ÆR6÷W&6R„7–æ2â“£¤÷WGWB"’°Ð¢6†÷v×FFÆrÒfÇ6S°Ð¢–b‡2å7&4f–ÇFW'5µ5$5ôÕEÒ’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õõ$TäDU$d”Åô4õ%%UC°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b‡6†÷v×FFÆr’°Ð¢6†÷tÖVF–G—W4F–Æör‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢T”åBW'#°Ð Ð¢7v—F6‚†‡"’°Ð¢66RUô$õ%C Ð¢66R$e5ôUô$õ%C Ð¢W'"Ò”E5ôÔ”äe$Õóƒ#°Ð¢'&V³°Ð¢66RUôd”Ã Ð¢66RUõô”åDU# Ð¢FVfVÇC Ð¢W'"Ò”E5ôÔ”äe$Õóƒ3°Ð¢'&V³°Ð¢66RUô”ådÄ”D$s Ð¢W'"Ò”E5ôÔ”äe$ÕóƒC°Ð¢'&V³°Ð¢66RUôõUDôdÔTÔõ%“ Ð¢W'"Ò”E5ôuôõUEôôeôÔTÔõ%“°Ð¢'&V³°Ð¢66RdeuôUô4ääõEô4ôääT5C Ð¢W'"Ò”E5ôÔ”äe$Õóƒc°Ð¢'&V³°Ð¢66RdeuôUô4ääõEôÄôEõ4õU$4Uôd”ÅDU# Ð¢W'"Ò”E5ôÔ”äe$Õóƒs°Ð¢'&V³°Ð¢66RdeuôUô4ääõEõ$TäDU# Ð¢W'"Ò”E5ôÔ”äe$Õóƒƒ°Ð¢'&V³°Ð¢66RdeuôUô”ådÄ”Eôd”ÄUôdõ$ÔC Ð¢W'"Ò”E5ôÔ”äe$Õóƒ“°Ð¢'&V³°Ð¢66RdeuôUôäõEôdõTäC Ð¢W'"Ò”E5ôÔ”äe$Õó“°Ð¢'&V³°Ð¢66RdeuôUõTä´äõtåôd”ÄUõE•S Ð¢W'"Ò”E5ôÔ”äe$Õó“°Ð¢'&V³°Ð¢66RdeuôUõTå5Uõ%DTEõ5E$TÓ Ð¢W'"Ò”E5ôÔ”äe$Õó“#°Ð¢'&V³°Ð¢66R$e5ôUôäõôd”ÄU3 Ð¢W'"Ò”E5õ$e5ôäõôd”ÄU3°Ð¢'&V³°Ð¢66R$e5ôUô4ôÕ$U54TC Ð¢W'"Ò”E5õ$e5ô4ôÕ$U54TC°Ð¢'&V³°Ð¢66R$e5ôUôTä5%•DTC Ð¢W'"Ò”E5õ$e5ôTä5%•DTC°Ð¢'&V³°Ð¢66R$e5ôUôÔ•54”äuõdôÅ3 Ð¢W'"Ò”E5õ$e5ôÔ•54”äuõdôÅ3°Ð¢'&V³°Ð¢ÐÐ Ð¢F‡&÷rW'#°Ð¢ÐÐ¢ÐÐ Ð¢–b†$Ö–äf–ÆR’°Ð¢&ööÂ$—5f–FVòÒfÇ6S°Ð¢&ööÂ—5$e2ÒfÇ6S°Ð¢57G&–æurVçG'•$e3°Ð Ð¢òò6†V6²f÷"7W÷'FVB–çFW&f6W0Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b“°Ð¢&ööÂg6bÒfÇ6S°Ð¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢òò”f–ÆU6÷W&6Tf–ÇFW Ð¢–b‚Õ÷e4b’°Ð¢Õ÷e4bÒ$c°Ð¢–b†Õ÷e4b’°Ð¢g6bÒG'VS°Ð¢–b‚Õ÷Ôå2’°Ð¢Õ÷Ôå2Ò$c°Ð¢ÐÐ¢–b‚Õ÷7Æ—GFW%52’°Ð¢Õ÷7Æ—GFW%52Ò$c°Ð¢ÐÐ¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢–b†6Ç6–BÓÒ4Å4”Eõ7F–ÆÅf–FVòÇÂ6Ç6–BÓÒ4Å4”EôÕ4–ÖvU6÷W&6R’°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÒVÇ6R–b†6Ç6–BÓÒõ÷WV–Föb„5$$f–ÆU6÷W&6R’’°Ð¢t4„"¢dâÒçVÆÇG#°Ð¢ÕôÔTD”õE•R×C°Ð¢–b…5T44TTDTB†Õ÷e4bÓävWD7W$f–ÆR‚gdâÂf×B’’bbdâbb§dâ’°Ð¢—5$e2ÒG'VS°Ð¢VçG'•$e2Òdã°Ð¢6õF6´ÖVÔg&VR‡dâ“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢òò”Õ7G&VÕ6VÆV7Bò”F—&V7Efö%7V Ð¢–b‚g6b’°Ð¢–b†6Ç6–BÓÒõ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’’°Ð¢Õ÷VF–õ7v—F6†W%52Ò$c°Ð¢ÒVÇ6R°Ð¢–b†6Ç6–BÓÒuT”EôÄe7Æ—GFW"’°Ð¢Õ÷7Æ—GFW%52Ò$c°Ð¢ÒVÇ6R°Ð¢–b†6Ç6–BÓÒ4Å4”Eõe4f–ÇFW"ÇÂ6Ç6–BÓÒ4Å4”Eõ‡•7V$f–ÇFW"’°Ð¢–b‚2ä—4•5$WFôÆöDVæ&ÆVB‚’’°Ð¢Õ÷Ee2Ò$c°Ð¢Õ÷Ee3"Ò$c°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†6Ç6–BÒ4Å4”EôÕ4$TVF–õ&VæFW&W"’°Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7CâFW7BÒ$b’°Ð¢–b‚Õ÷÷F†W%55³Ò’°Ð¢Õ÷÷F†W%55³ÒÒ$c°Ð¢ÒVÇ6R–b‚Õ÷÷F†W%55³Ò’°Ð¢Õ÷÷F†W%55³ÒÒ$c°Ð¢ÒVÇ6R°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢òò÷F†W'0Ð¢–b‚Õ÷Äã#’°Ð¢Õ÷Äã#Ò$c°Ð¢ÐÐ¢–b‚Õ÷´d’’°Ð¢Õ÷´d’Ò$c°Ð¢ÐÐ¢–b‚Õ÷Ôõ’°Ð¢Õ÷ÔõÒ$c°Ð¢ÐÐ¢–b‚Õ÷ÔÔ5³Ò’°Ð¢Õ÷ÔÔ5³ÒÒ$c°Ð¢ÒVÇ6R–b‚Õ÷ÔÔ5³Ò’°Ð¢Õ÷ÔÔ5³ÒÒ$c°Ð¢ÐÐ¢–b†Õö%W6U6VVµ&Wf–Wrbb$—5f–FVòbb—5f–FVõ&VæFW&W"‡$b’’°Ð¢$—5f–FVòÒG'VS°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢54U%B†Õ÷e4bÇÂÕöd7W7FöÔw&‚“°Ð Ð¢–b‚$—5f–FVò’°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ¢–b†Õö%W6U6VVµ&Wf–Wrbb—4–ÖvTf–ÆR†fâ’’°Ð¢òòFöâwBW6R&Wf–Wrf÷"–ÖvW0Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ Ð¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢…$U5TÅB&Wf–Wt…#°Ð¢–b†—5$e2’°Ð¢46öÕG#Ä4dtÖævW#âfv×Ò7FF–5ö67CÄ4dtÖævW"£â†Õ÷t%÷&Wf–Wrç“°Ð¢&Wf–Wt…"Òfv×Óå&VæFW%$e4f–ÆTVçG'’†fâÂçVÆÇG"ÂVçG'•$e2“°Ð¢ÒVÇ6R°Ð¢&Wf–Wt…"ÒÕ÷t%÷&Wf–WrÓå&VæFW$f–ÆR†fâÂçVÆÇG"“°Ð¢ÐÐ Ð¢–b„d”ÄTB‡&Wf–Wt…"’’°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢&VÆV6U&Wf–Wtw&‚‚“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R²òòVF–òET Ð¢òò6†V6²f÷"7W÷'FVB–çFW&f6W0Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b“°Ð¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢–b†6Ç6–BÓÒuT”EôÄe7Æ—GFW"ÇÂ6Ç6–BÓÒuT”EôÄe7Æ—GFW%6÷W&6R’°Ð¢Õ÷7Æ—GFW$GV%52Ò$c°Ð¢–b†Õ÷7Æ—GFW%52bbÕ÷7Æ—GFW%52ÓÒÕ÷7Æ—GFW$GV%52’°Ð¢Õ÷7Æ—GFW$GV%52å&VÆV6R‚“°Ð¢ÐÐ¢ÒVÇ6R–b†6Ç6–BÓÒõ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’’°Ð¢–b‚Õ÷VF–õ7v—F6†W%52’°Ð¢Õ÷VF–õ7v—F6†W%52Ò$c°Ð¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð¢ÐÐ Ð¢òòvRFöâwB¶VWG&6²öb—VB–çWG26–æ6RF†B†&FÇ’Ö¶W2ç’6Vç6PÐ¢–b‡2æd¶VW†—7F÷'’bbfâäf–æB…õB‚'—S¢"’’ÒbbôdBÓæ$FEFõ&V6VçB’°Ð¢–b†$Ö–äf–ÆR’°Ð¢WFò¢Õ%RÒg2äÕ%S°Ð¢&V6VçDf–ÆTVçG'’#°Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’’°Ð¢–b‡Æ’æÕö%–÷WGV&TDÂbbÆ’æÕ÷–FÅ6÷W&6UU$Âä—4V×G’‚’’°Ð¢Õ%RÓäÆöDÖVF–†—7F÷'”VçG'”dâ‡Æ’æÕ÷–FÅ6÷W&6UU$ÂÂ"“°Ð¢ÒVÇ6R°Ð¢Õ%RÓäÆöDÖVF–†—7F÷'”VçG'”dâ†fâÂ"“°Ð¢–b‡Æ’æÕöfç2ävWD6÷VçB‚’â"æfç2ävWD6÷VçB‚’’°Ð¢"æfç2å&VÖ÷fTÆÂ‚“°Ð¢"æfç2äFD†VDÆ—7B‚gÆ’æÕöfç2“°Ð¢ÐÐ¢–b‚2ä—4W†6ÇVFVDg&öÔ†—7F÷'’†fâ’’°Ð¢4„FEFõ&V6VçDFö72…4„$EõD‚Âfâ“°Ð¢ÐÐ¢ÐÐ¢–b‡Æ’æÕö7VR’°Ð¢"æ7VRÒÆ’æÕö7VUöf–ÆVæÖS°Ð¢ÐÐ¢–b‡Æ’æÕ÷7V'2ävWD6÷VçB‚’â"ç7V'2ävWD6÷VçB‚’’°Ð¢"ç7V'2å&VÖ÷fTÆÂ‚“°Ð¢"ç7V'2äFD†VDÆ—7B‚gÆ’æÕ÷7V'2“°Ð¢ÐÐ Ð¢–b‡Æ’æÕöÆ&VÂä—4V×G’‚’’°Ð¢57G&–ærF—FÆS°Ð¢f÷"†6öç7BWFòbÔÔ2¢Õ÷ÔÔ2’°Ð¢–b‡ÔÔ2’°Ð¢46öÔ%5E"'7G#°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEõF—FÆR‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢F—FÆRÒ'7G"æÕ÷7G#°Ð¢F—FÆRåG&–Ò‚“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b‡F—FÆRävWDÆVæwF‚‚’ãÒbb—4æÖU6–Ö–Æ"‡F—FÆRÂF…WF–Ç3£¥7G&—F„÷%W&Â†fâ’’’°Ð¢"çF—FÆRÒF—FÆS°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b‡Æ’æÕö%–÷WGV&TDÂÇÂ—4æÖU6–Ö–Æ"‡Æ’æÕöÆ&VÂÂF…WF–Ç3£¥7G&—F„÷%W&Â†fâ’’’°Ð¢–b‚Æ’æÕö%–÷WGV&TDÂÇÂfâÓÒÆ’æÕ÷–FÅ6÷W&6UU$Â’°Ð¢"çF—FÆRÒÆ’æÕöÆ&VÃ°Ð¢ÒVÇ6R°Ð¢57G&–ærf–FVôæÖR‡Æ’æÕöÆ&VÂ“°Ð¢–çBÒÒÆ7D–æFW„öd57G&–ær‡f–FVôæÖRÂõB‚"‚"’“°Ð¢–b†Òâ’°Ð¢f–FVôæÖRÒÆ’æÕöÆ&VÂäÆVgB†Ò“°Ð¢ÐÐ¢"çF—FÆRÒf–FVôæÖS°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢54U%B†fÇ6R“°Ð¢"æfç2äFD†VB†fâ“°Ð¢ÐÐ Ð¢Õ%RÓäFB‡"ÂG'VR“°Ð¢57G&–æurÆ”Æ—7DæÖS°Ð¢–b‡2æ%&VÖVÖ&W$W‡FW&æÅÆ–Æ—7E÷2bbÕ÷væEÆ–Æ—7D&"ä—4W‡FW&æÅÆ”Æ—7D7F—fR‡Æ”Æ—7DæÖR’’°Ð¢2å6fUÆ”Æ—7E÷6—F–öâ‡Æ”Æ—7DæÖRÂÕ÷væEÆ–Æ—7D&"ävWE6VÄ–G‚‚’“°Ð¢ÐÐ¢ÐÐ¢VÇ6R°Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b‚Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’ÇÂÆ’æÕö%–÷WGV&TDÂ’°Ð¢5&V6VçDf–ÆTÆ—7B¢Õ%TGV"Òg2äÕ%TGV#°Ð¢Õ%TGV"Óå&VDÆ—7B‚“°Ð¢Õ%TGV"ÓäFB†fâ“°Ð¢Õ%TGV"Óåw&—FTÆ—7B‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢$Ö–äf–ÆRÒfÇ6S°Ð Ð¢–b†Õöd7W7FöÔw&‚’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢–b‡2æe&W÷'Df–ÆVE–ç2’°Ð¢6†÷tÖVF–G—W4F–Æör‚“°Ð¢ÐÐ Ð¢6WGW6†FW'2‚“°Ð Ð¢6WEÆ–&6´ÖöFR…Õôd”ÄR“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWW‡FW&æÄ6†FW'2‚Ð§°Ð¢òòå„4…†U‡FW&æÂ4†FW'2’f–ÆRf÷&ÖC Ð¢òòÒUDbÓ‚FW‡Bf–ÆRàÐ¢òòÒÆö6FVB–â6ÖRföÆFW"2F†RVF–ò÷f–FVòf–ÆRÂæB†26ÖR&6Rf–ÆVæÖRàÐ¢òòÒ—Bv–ÆÂ÷fW'&–FR6†FW"ÖWFFFF†B—2VÖ&VFFVB–âF†Rf–ÆRàÐ¢òòÒV6‚Æ–æRFVf–æW26†FW#¢F–ÖV6öFRÂ÷F–öæÆÇ’föÆÆ÷vVB'’76RæB6†FW"F—FÆRàÐ¢òòÒF–ÖV6öFR×W7B&R–âF†—2f÷&ÖC¢„ƒ¤ÔÓ¥52ÆFF@Ð Ð¢57G&–ærfâÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‡G'VR“°Ð¢–b†fâä—4V×G’‚’ÇÂF…WF–Ç3£¤—5U$Â†fâ’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢5F‚7†fâ“°Ð¢–b‚7å&VæÖTW‡FVç6–öâ…õB‚"ç†6‡"’’ÇÂ7äf–ÆTW†—7G2‚’’°Ð¢&WGW&ã°Ð¢ÐÐ¢fâÒ7æÕ÷7G%Fƒ°Ð Ð¢5FW‡Df–ÆRb„5FW‡Df–ÆS£¥UDc‚“°Ð¢bå6WDfÆÆ&6´Væ6öF–ær„5FW‡Df–ÆS£¤å4’“°Ð Ð¢57G&–ær7G#°Ð¢–b‚bä÷Vâ†fâ’ÇÂbå&VE7G&–ær‡7G"’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢bå6VV²ƒÂ4f–ÆS£¥6VVµ÷6—F–öã£¦&Vv–â“°Ð Ð¢v†–ÆR†bå&VE7G&–ær‡7G"’’°Ð¢$TdU$Tä4UõD”ÔR'BÒ°Ð¢57G&–æræÖRÒ"#°Ð Ð¢–b‡7G"ävWDÆVæwF‚‚’â’°Ð¢–çBÄ†÷W"Ò°Ð¢–çBÄÖ–çWFRÒ°Ð¢–çBÅ6V6öæBÒ°Ð¢–çBÄÖ–ÆÆ—6V2Ò°Ð¢–b…÷7G66æe÷2‡7G"äÆVgBƒ"’ÂõB‚"S&C¢S&C¢S&BÂS6B"’ÂfÄ†÷W"ÂfÄÖ–çWFRÂfÅ6V6öæBÂfÄÖ–ÆÆ—6V2’ÓÒB’°Ð¢'BÒ‚‚‚†Ä†÷W"¢c’²ÄÖ–çWFR’¢c²Å6V6öæB’¢Ô”ÄÄ•4T4ôäE2²ÄÖ–ÆÆ—6V2’¢…Tä•E2òÔ”ÄÄ•4T4ôäE2“°Ð¢–b‡7G"ävWDÆVæwF‚‚’â"’°Ð¢æÖRÒ7G"äÖ–Bƒ"“°Ð¢æÖRåG&–Ò‚“°Ð¢ÐÐ¢Õ÷4"Óä6†VæB‡'BÂæÖR“°Ð¢ÒVÇ6R°Ð¢'&V³°Ð¢ÐÐ¢ÒVÇ6R°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢Õ÷4"Óä6†6÷'B‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW6†FW'2‚Ð§°Ð¢òò&VÆV6RF†RöÆB6†FW"&ræB7&VFRæWröæRàÐ¢òòGVRFò6Ö'Bö–çFW'2F†RöÆB6†FW"&rvöâw@Ð¢òò&RFVÆWFVBVçF–ÂÆÂ6Æ76W2&VÆV6R—BàÐ¢Õ÷4"å&VÆV6R‚“°Ð¢Õ÷4"ÒDT%TuôäUr4E4Ô6†FW$&r†çVÆÇG"ÂçVÆÇG"“°Ð Ð¢6WGWW‡FW&æÄ6†FW'2‚“°Ð¢–b†Õ÷4"Óä6†vWD6÷VçB‚’â’°Ð¢WFFU6VV¶&$6†FW$&r‚“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òòFôFó¢FBvÆö&Âö–çFW"Æ—7Bf÷"”E4Ô6†FW$&pÐ¢4–çFW&f6TÆ—7CÄ”&6Tf–ÇFW#â$g3°Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b“°Ð¢$g2äFEF–Â‡$b“°Ð¢VæDVçVÔf–ÇFW'3°Ð Ð¢õ4•D”ôâ÷3°Ð Ð¢÷2Ò$g2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2bbÕ÷4"Óä6†vWD6÷VçB‚’’°Ð¢”&6Tf–ÇFW"¢$bÒ$g2ävWDæW‡B‡÷2“°Ð Ð¢46öÕ•G#Ä”E4Ô6†FW$&sâ4"Ò$c°Ð¢–b‚4"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢f÷"„Etõ$B’ÒÂ6çBÒ4"Óä6†vWD6÷VçB‚“²’Â6çC²’²²’°Ð¢$TdU$Tä4UõD”ÔR'C°Ð¢46öÔ%5E"æÖS°Ð¢–b…5T44TTDTB‡4"Óä6†vWB†’Âg'BÂfæÖR’’’°Ð¢Õ÷4"Óä6†VæB‡'BÂæÖR“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢÷2Ò$g2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2bbÕ÷4"Óä6†vWD6÷VçB‚’’°Ð¢”&6Tf–ÇFW"¢$bÒ$g2ävWDæW‡B‡÷2“°Ð Ð¢46öÕ•G#Ä”6†FW$–æfóâ4’Ò$c°Ð¢–b‚4’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢4„"—6óc3“³5Ó°Ð¢£¤vWDÆö6ÆT–æfô„Äô4ÄUõU4U%ôDTdTÅBÂÄô4ÄUõ4•4óc3”ÄätäÔRÂ—6óc3“Â2“°Ð¢57G&–æt—6óc3“"Ò•4ôÆæs£¤•4óc3“Fóc3“"†—6óc3““°Ð¢–b†—6óc3“"ävWDÆVæwF‚‚’Â2’°Ð¢—6óc3“"Ò&Vær#°Ð¢ÐÐ Ð¢T”åB6çBÒ4’ÓävWD6†FW$6÷VçB„4„DU%õ$ôõEô”B“°Ð¢f÷"…T”åB’Ò²’ÃÒ6çC²’²²’°Ð¢T”åB6–BÒ4’ÓävWD6†FW$–B„4„DU%õ$ôõEô”BÂ’“°Ð Ð¢6†FW$VÆVÖVçB6S°Ð¢–b‡4’ÓävWD6†FW$–æfò†6–BÂf6R’’°Ð¢6†"Å³5ÒÒ¶—6óc3“%³ÒÂ—6óc3“%³ÒÂ—6óc3“%³%×Ó°Ð¢6†"65µÒÒ"#°Ð¢46öÔ%5E"æÖS°Ð¢æÖRäGF6‚‡4’ÓävWD6†FW%7G&–æt–æfò†6–BÂÂÂ62’“°Ð¢Õ÷4"Óä6†VæB†6Rç'E7F'BÂæÖR“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢÷2Ò$g2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2bbÕ÷4"Óä6†vWD6÷VçB‚’’°Ð¢”&6Tf–ÇFW"¢$bÒ$g2ävWDæW‡B‡÷2“°Ð Ð¢46öÕ•G#Ä”ÔW‡FVæFVE6VV¶–ærÂd””Eô”ÔW‡FVæFVE6VV¶–æsâU2Ò$c°Ð¢–b‚U2’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢ÆöærÖ&¶W$6÷VçBÒ°Ð¢–b…5T44TTDTB‡U2ÓævWEôÖ&¶W$6÷VçB‚dÖ&¶W$6÷VçB’’’°Ð¢f÷"†Æöær’Ò²’ÃÒÖ&¶W$6÷VçC²’²²’°Ð¢F÷V&ÆRÖ&¶W%F–ÖRÒ°Ð¢–b…5T44TTDTB‡U2ÓävWDÖ&¶W%F–ÖR†’ÂdÖ&¶W%F–ÖR’’’°Ð¢57G&–æuræÖS°Ð¢æÖRäf÷&ÖB„”E5ôuô4„DU"Â’“°Ð Ð¢46öÔ%5E"'7G#°Ð¢–b…5ôô²ÓÒU2ÓävWDÖ&¶W$æÖR†’Âf'7G"’’°Ð¢æÖRÒ'7G#°Ð¢ÐÐ Ð¢Õ÷4"Óä6†VæB…$TdU$Tä4UõD”ÔR„Ö&¶W%F–ÖR¢’ÂæÖR“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’bbÆ’æÕö7VR’°Ð¢6WGW7VT6†FW'2‡Æ’æÕö7VUöf–ÆVæÖR“°Ð¢ÐÐ Ð¢WFFU6VV¶&$6†FW$&r‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW7VT6†FW'2„57G&–ær7VVfâ’°Ð¢57G&–ær7G#°Ð¢–çB7VUö–æFW‚‚Ó“°Ð Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b‚Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’’°Ð¢54U%B†fÇ6R“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢5vV%FW‡Df–ÆRb„5FW‡Df–ÆS£¥UDc‚“°Ð¢bå6WDfÆÆ&6´Væ6öF–ær„5FW‡Df–ÆS£¤å4’“°Ð¢–b‚bä÷Vâ†7VVfâ’ÇÂbå&VE7G&–ær‡7G"’’°Ð¢&WGW&ã°Ð¢ÐÐ¢bå6VV²ƒÂ4f–ÆS£¥6VVµ÷6—F–öã£¦&Vv–â“°Ð Ð¢57G&–ær&6S°Ð¢&ööÂ—7W&ÂÒF…WF–Ç3£¤—5U$Â†7VVfâ“°Ð¢–b†—7W&Â’°Ð¢–çBÒ7VVfâäf–æB…õB‚sòr’“°Ð¢–b‡â’°Ð¢7VVfâÒ7VVfâäÆVgB‡“°Ð¢ÐÐ¢Ò7VVfâå&WfW'6Tf–æB…õB‚ròr’“°Ð¢–b‡â’°Ð¢&6RÒ7VVfâäÆVgB‡²“°Ð¢ÐÐ¢ÐÐ¢VÇ6R°Ð¢5F‚&6Vf–ÆWF‚†7VVfâ“°Ð¢&6Vf–ÆWF‚å&VÖ÷fTf–ÆU7V2‚“°Ð¢&6Vf–ÆWF‚äFD&6·6Æ6‚‚“°Ð¢&6RÒ&6Vf–ÆWF‚æÕ÷7G%Fƒ°Ð¢ÐÐ Ð¢57G&–ærF—FÆS°Ð¢57G&–ærW&f÷&ÖW#°Ð¢4FÄÆ—7CÄ7VUG&6´ÖWFâG&6¶Ã°Ð¢7VUG&6´ÖWFG&6³°Ð¢–çBG&6´”Bƒ“°Ð¢57G&–ærÆ7Ff–ÆS°Ð Ð¢v†–ÆR†bå&VE7G&–ær‡7G"’’°Ð¢7G"åG&–Ò‚“°Ð¢–b†7VUö–æFW‚ÓÒÓbb7G"äÆVgBƒR’ÓÒõB‚%D•DÄR"’’°Ð¢F—FÆRÒ7G"äÖ–Bƒb’åG&–Ò…õB‚%Â""’“°Ð¢ÐÐ¢VÇ6R–b†7VUö–æFW‚ÓÒÓbb7G"äÆVgBƒ’’ÓÒõB‚%U$dõ$ÔU""’’°Ð¢W&f÷&ÖW"Ò7G"äÖ–Bƒ’åG&–Ò…õB‚%Â""’“°Ð¢ÐÐ¢VÇ6R–b‡7G"äÆVgBƒB’ÓÒõB‚$d”ÄR"’’°Ð¢–b‡7G"å&–v‡BƒB’ÓÒõB‚%tdR"’ÇÂ7G"å&–v‡Bƒ2’ÓÒõB‚$Õ2"’ÇÂ7G"å&–v‡BƒB’ÓÒõB‚$dÄ2"’ÇÂ7G"å&–v‡BƒB’ÓÒõB‚$”db"’’°Ð¢57G&–ærf–ÆUöVçG'“°Ð¢–b‡7G"å&–v‡Bƒ2’ÓÒõB‚$Õ2"’’°Ð¢f–ÆUöVçG'’Ò7G"äÖ–BƒRÂ7G"ävWDÆVæwF‚‚’Ò’’åG&–Ò…õB‚%Â""’“°Ð¢ÒVÇ6R°Ð¢f–ÆUöVçG'’Ò7G"äÖ–BƒRÂ7G"ävWDÆVæwF‚‚’Ò’åG&–Ò…õB‚%Â""’“°Ð¢ÐÐ¢–b†f–ÆUöVçG'’ÒÆ7Ff–ÆR’°Ð¢7VUö–æFW‚²³°Ð¢Æ7Ff–ÆRÒf–ÆUöVçG'“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢VÇ6R–b†7VUö–æFW‚ãÒ’°Ð¢–b‡7G"äÆVgBƒR’ÓÒõB‚%E$4²"’bb7G"å&–v‡BƒR’ÓÒõB‚$TD”ò"’’°Ð¢5C$4F×‡7G"äÖ–BƒbÂ7G"ävWDÆVæwF‚‚’Ò"’“°Ð¢6öç7B6†"¢F×"‡F×“°Ð¢766æe÷2‡F×"Â"VB"ÂgG&6´”B“°Ð¢–b‡G&6²çG&6´”BÒ’°Ð¢G&6¶ÂäFEF–Â‡G&6²“°Ð¢G&6²Ò7VUG&6´ÖWF‚“°Ð¢ÐÐ¢G&6²çG&6´”BÒG&6´”C°Ð¢G&6²æf–ÆT”BÒ7VUö–æFWƒ°Ð¢ÐÐ¢VÇ6R–b‡7G"äÆVgBƒR’ÓÒõB‚%D•DÄR"’’°Ð¢G&6²çF—FÆRÒ7G"äÖ–Bƒb’åG&–Ò…õB‚%Â""’“°Ð¢ÐÐ¢VÇ6R–b‡7G"äÆVgBƒ’’ÓÒõB‚%U$dõ$ÔU""’’°Ð¢G&6²çW&f÷&ÖW"Ò7G"äÖ–Bƒ’åG&–Ò…õB‚%Â""’“°Ð¢ÐÐ¢VÇ6R–b‡7G"äÆVgBƒR’ÓÒõB‚$”äDU‚"’’°Ð¢5C$4F×‡7G"äÖ–Bƒb’“°Ð¢6öç7B6†"¢F×"‡F×“°Ð¢–çB“ƒ’ÂÒƒ’Â2ƒ’Â×2ƒ“°Ð¢766æe÷2‡F×"Â"VBVC¢VC¢VB"Âf“ÂfÒÂg2Âf×2“°Ð¢–b†“Ò’G&6²çF–ÖRÒ“cB¢‚†Ò¢c²2’¢²×2“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b‡G&6²çG&6´”BÒ’°Ð¢G&6¶ÂäFEF–Â‡G&6²“°Ð¢ÐÐ Ð¢–b‡G&6¶ÂävWD6÷VçB‚’ãÒ’°Ð¢õ4•D”ôâÒG&6¶ÂävWD†VE÷6—F–öâ‚“°Ð¢&ööÂ"‡G'VR“°Ð¢Fò°Ð¢–b‡ÓÒG&6¶ÂävWEF–Å÷6—F–öâ‚’’"ÒfÇ6S°Ð¢7VUG&6´ÖWF2‡G&6¶ÂävWDæW‡B‡’“°Ð¢–b†7VUö–æFW‚ÓÒÇÂ†7VUö–æFW‚âbb2æf–ÆT”BÓÒÆ’æÕö7VUö–æFW‚’’°Ð¢57G&–ærÆ&VÃ°Ð¢–b‚2çF—FÆRä—4V×G’‚’’°Ð¢Æ&VÂÒ2çF—FÆS°Ð¢–b‚2çW&f÷&ÖW"ä—4V×G’‚’’°Ð¢Æ&VÂ³Ò…õB‚"Ò"’²2çW&f÷&ÖW"“°Ð¢ÐÐ¢VÇ6R–b‚W&f÷&ÖW"ä—4V×G’‚’’°Ð¢Æ&VÂ³Ò…õB‚"Ò"’²W&f÷&ÖW"“°Ð¢ÐÐ¢ÐÐ¢Õ÷4"Óä6†VæB†2çF–ÖRÂÆ&VÂ“°Ð¢ÐÐ¢Òv†–ÆR†"“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWEdD6†FW'2‚Ð§°Ð¢òò&VÆV6RF†RöÆB6†FW"&ræB7&VFRæWröæRàÐ¢òòGVRFò6Ö'Bö–çFW'2F†RöÆB6†FW"&rvöâw@Ð¢òò&RFVÆWFVBVçF–ÂÆÂ6Æ76W2&VÆV6R—BàÐ¢Õ÷4"å&VÆV6R‚“°Ð¢Õ÷4"ÒDT%TuôäUr4E4Ô6†FW$&r†çVÆÇG"ÂçVÆÇG"“°Ð Ð¢t4„"'Vfe´Ô…õD…Ó°Ð¢TÄôärÆVâÂVÄçVÔöd6†FW'3°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö3°Ð Ð¢–b†Õ÷EdD’bb5T44TTDTB†Õ÷EdD’ÓävWDEdDF—&V7F÷'’†'VfbÂö6÷VçFöb†'Vfb’ÂfÆVâ’Ð¢bb5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚fÆö2’Ð¢bb5T44TTDTB†Õ÷EdD’ÓävWDçVÖ&W$öd6†FW'2†Æö2åF—FÆTçVÒÂgVÄçVÔöd6†FW'2’’’°Ð¢57G&–ærFƒ°Ð¢F‚äf÷&ÖB„Â"W5ÅÇf–FVõ÷G2ä”dò"Â'Vfb“°Ð¢TÄôäreE4âÂEDã°Ð Ð¢–b„5fö$f–ÆS£¤vWEF—FÆT–æfò‡F‚ÂÆö2åF—FÆTçVÒÂeE4âÂEDâ’’°Ð¢F‚äf÷&ÖB„Â"W5ÅÅeE5òS&ÇUóä”dò"Â'VfbÂeE4â“°Ð¢4FÄÆ—7CÄ57G&–æsâf–ÆW3°Ð Ð¢5fö$f–ÆRfö#°Ð¢–b‡fö"ä÷Vâ‡F‚Âf–ÆW2ÂEDâÂfÇ6R’’°Ð¢–çB”6†FW'46÷VçBÒfö"ävWD6†FW'46÷VçB‚“°Ð¢–b‡VÄçVÔöd6†FW'2ÓÒ…TÄôär–”6†FW'46÷VçB’°Ð¢f÷"†–çB’Ò²’Â”6†FW'46÷VçC²’²²’°Ð¢$TdU$Tä4UõD”ÔR'BÒfö"ävWD6†FW$öfg6WB†’“°Ð Ð¢57G&–æur7G#°Ð¢7G"äf÷&ÖB„”E5ôuô4„DU"Â’²“°Ð Ð¢Õ÷4"Óä6†VæB‡'BÂ7G"“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢òò'6W"f–ÆVBÐ¢54U%B„dÅ4R“°Ð¢ÐÐ¢fö"ä6Æ÷6R‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢Õ÷4"Óä6†6÷'B‚“°Ð Ð¢WFFU6VV¶&$6†FW$&r‚“°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷VäEdB„÷VäEdDFF¢ôDBÐ§°Ð¢Æ7D÷Väf–ÆRäV×G’‚“°Ð Ð¢57G&–æurfâÒ57G&–æur‡ôDBÓçF‚“°Ð¢…$U5TÅB‡"ÒÕ÷t"Óå&VæFW$f–ÆR†fâÂçVÆÇG"“°Ð Ð¢–b…5T44TTDTB†‡"’’°Ð¢Æ7D÷Väf–ÆRÒfã°Ð¢ÐÐ Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b‡2æe&W÷'Df–ÆVE–ç2’°Ð¢6†÷tÖVF–G—W4F–Æör‚“°Ð¢ÐÐ Ð¢–b…5T44TTDTB†‡"’bbÕö%W6U6VVµ&Wf–Wr’°Ð¢–b„d”ÄTB†‡"ÒÕ÷t%÷&Wf–WrÓå&VæFW$f–ÆR‡ôDBÓçF‚ÂçVÆÇG"’’’°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ¢ÐÐ Ð¢òò6†V6²f÷"7W÷'FVB–çFW&f6W0Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$bÐ¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢òòEdB7GVf`Ð¢–b‚Õ÷EdD2’°Ð¢Õ÷EdD2Ò$c°Ð¢ÐÐ¢–b‚Õ÷EdD’’°Ð¢Õ÷EdD’Ò$c°Ð¢ÐÐ¢òò”Õ7G&VÕ6VÆV7Bf–ÇFW'2ò”F—&V7Efö%7V Ð¢–b†6Ç6–BÓÒõ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’’°Ð¢Õ÷VF–õ7v—F6†W%52Ò$c°Ð¢ÒVÇ6R°Ð¢–b†6Ç6–BÓÒ4Å4”Eõe4f–ÇFW"ÇÂ6Ç6–BÓÒ4Å4”Eõ‡•7V$f–ÇFW"’°Ð¢–b‚2ä—4•5$WFôÆöDVæ&ÆVB‚’’°Ð¢Õ÷Ee2Ò$c°Ð¢Õ÷Ee3"Ò$c°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†6Ç6–BÒ4Å4”EôÕ4$TVF–õ&VæFW&W"’°Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7CâFW7BÒ$b’°Ð¢–b‚Õ÷÷F†W%55³Ò’°Ð¢Õ÷÷F†W%55³ÒÒ$c°Ð¢ÒVÇ6R–b‚Õ÷÷F†W%55³Ò’°Ð¢Õ÷÷F†W%55³ÒÒ$c°Ð¢ÒVÇ6R°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢òò÷F†W'0Ð¢–b‚Õ÷Äã#’°Ð¢Õ÷Äã#Ò$c°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢54U%B†Õ÷EdD2“°Ð¢54U%B†Õ÷EdD’“°Ð Ð¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t%÷&Wf–WrÂTbÂ$b’°Ð¢–b‚†Õ÷EdD5÷&Wf–WrÒ$b’bb†Õ÷EdD•÷&Wf–WrÒ$b’’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð¢ÐÐ Ð¢–b†‡"ÓÒUô”ådÄ”D$r’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó“3°Ð¢ÒVÇ6R–b†‡"ÓÒdeuôUô4ääõEõ$TäDU"’°Ð¢F‡&÷r…T”åB””E5ôEdEôäeôÄÅõ”å5ôU%$õ#°Ð¢ÒVÇ6R–b†‡"ÓÒdeuõ5õ%D”Åõ$TäDU"’°Ð¢F‡&÷r…T”åB””E5ôEdEôäeõ4ôÔUõ”å5ôU%$õ#°Ð¢ÒVÇ6R–b†‡"ÓÒUôäô”åDU$d4RÇÂÕ÷EdD2ÇÂÕ÷EdD’’°Ð¢F‡&÷r…T”åB””E5ôEdEô”åDU$d4U5ôU%$õ#°Ð¢ÒVÇ6R–b†‡"ÓÒdeuôUô4ääõEôÄôEõ4õU$4Uôd”ÅDU"’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó“C°Ð¢ÒVÇ6R–b„d”ÄTB†‡"’’°Ð¢F‡&÷r…T”åB””E5ôuôd”ÄTC°Ð¢ÐÐ Ð¢t4„"'Vfe´Ô…õD…Ó°Ð¢TÄôärÆVâÒ°Ð¢–b…5T44TTDTB†‡"ÒÕ÷EdD’ÓävWDEdDF—&V7F÷'’†'VfbÂö6÷VçFöb†'Vfb’ÂfÆVâ’’’°Ð¢ôDBÓçF—FÆRÒ57G&–ær„57G&–æur†'Vfb’’åG&–Õ&–v‡B…õB‚%ÅÂ"’“°Ð¢ÐÐ Ð¢–b‡2æd¶VW†—7F÷'’’°Ð¢TÄôätÄôärÆÄEdDwV–C°Ð¢–b†Õ÷EdD’bb5T44TTDTB†Õ÷EdD’ÓävWDF—64”B†çVÆÇG"ÂfÆÄEdDwV–B’’’°Ð¢WFò¢Õ%RÒg2äÕ%S°Ð¢Õ%RÓäFB‡ôDBÓçF—FÆRÂÆÄEdDwV–B“°Ð¢ÐÐ¢–b‚2ä—4W†6ÇVFVDg&öÔ†—7F÷'’‡ôDBÓçF—FÆR’’°Ð¢4„FEFõ&V6VçDFö72…4„$EõD‚ÂôDBÓçF—FÆR“°Ð¢ÐÐ¢ÐÐ Ð¢òòDôDó¢&W6WFGf@Ð¢Õ÷EdD2Óå6WD÷F–öâ„EdEõ&W6WDöå7F÷ÂdÅ4R“°Ð¢Õ÷EdD2Óå6WD÷F–öâ„EdEô„Õ4eõF–ÖT6öFTWfVçG2ÂE%TR“°Ð Ð¢–b†Õö%W6U6VVµ&Wf–WrbbÕ÷EdD5÷&Wf–Wr’°Ð¢Õ÷EdD5÷&Wf–WrÓå6WD÷F–öâ„EdEõ&W6WDöå7F÷ÂdÅ4R“°Ð¢Õ÷EdD5÷&Wf–WrÓå6WD÷F–öâ„EdEô„Õ4eõF–ÖT6öFTWfVçG2ÂE%TR“°Ð¢ÐÐ Ð¢–b‡2æ–DÖVçTÆær’°Ð¢Õ÷EdD2Óå6VÆV7DFVfVÇDÖVçTÆæwVvR‡2æ–DÖVçTÆær“°Ð¢ÐÐ¢–b‡2æ–DVF–ôÆær’°Ð¢Õ÷EdD2Óå6VÆV7DFVfVÇDVF–ôÆæwVvR‡2æ–DVF–ôÆærÂEdEôTEôU…Eôæ÷E7V6–f–VB“°Ð¢ÐÐ¢–b‡2æ–E7V'F—FÆW4Æær’°Ð¢Õ÷EdD2Óå6VÆV7DFVfVÇE7V'–7GW&TÆæwVvR‡2æ–E7V'F—FÆW4ÆærÂEdEõ5ôU…Eôæ÷E7V6–f–VB“°Ð¢ÐÐ Ð¢Õö”EdDFöÖ–âÒEdEôDôÔ”åõ7F÷°Ð Ð¢6WEÆ–&6´ÖöFR…ÕôEdB“°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð¤…$U5TÅB4Ö–äg&ÖS£¤÷Vä$Dw&‚‚Ð§°Ð¢Æ7D÷Väf–ÆRäV×G’‚“°Ð Ð¢…$U5TÅB‡"ÒÕ÷t"Óå&VæFW$f–ÆR„Â""ÂÂ""“°Ð¢–b…5T44TTDTB†‡"’’°Ð¢6WEÆ–&6´ÖöFR…ÕôD”t•DÅô4EU$R“°Ð¢Õ÷Ed%7FFRÒ7FC£¦Ö¶U÷Væ—VSÄEd%7FFSâ‚“°Ð Ð¢òò6†V6²f÷"7W÷'FVB–çFW&f6W0Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b“°Ð¢&ööÂg6bÒfÇ6S°Ð¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢òò”f–ÆU6÷W&6Tf–ÇFW Ð¢–b‚Õ÷e4b’°Ð¢Õ÷e4bÒ$c°Ð¢–b†Õ÷e4b’°Ð¢g6bÒG'VS°Ð¢–b‚Õ÷Ôå2’°Ð¢Õ÷Ôå2Ò$c°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢òò”Õ7G&VÕ6VÆV7Bò”F—&V7Efö%7V Ð¢–b‚g6b’°Ð¢–b†6Ç6–BÓÒõ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’’°Ð¢Õ÷VF–õ7v—F6†W%52Ò$c°Ð¢ÒVÇ6R°Ð¢–b†6Ç6–BÓÒ4Å4”Eõe4f–ÇFW"ÇÂ6Ç6–BÓÒ4Å4”Eõ‡•7V$f–ÇFW"’°Ð¢–b‚g„vWD6WGF–æw2‚’ä—4•5$WFôÆöDVæ&ÆVB‚’’°Ð¢Õ÷Ee2Ò$c°Ð¢Õ÷Ee3"Ò$c°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢òò÷F†W'0Ð¢–b‚Õ÷Äã#’°Ð¢Õ÷Äã#Ò$c°Ð¢ÐÐ¢–b‚Õ÷ÔÔ5³Ò’°Ð¢Õ÷ÔÔ5³ÒÒ$c°Ð¢ÒVÇ6R–b‚Õ÷ÔÔ5³Ò’°Ð¢Õ÷ÔÔ5³ÒÒ$c°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢54U%B†Õ÷e4b“°Ð Ð¢òò$Dw&‚'V–ÆFW"–×ÆVÖVçG2”Õ7G&VÕ6VÆV7@Ð¢Õ÷7Æ—GFW%52ÒÕ÷t#°Ð¢ÐÐ¢&WGW&â‡#°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Vä6GW&R„÷VäFWf–6TFF¢ôDBÐ§°Ð¢Æ7D÷Väf–ÆRäV×G’‚“°Ð Ð¢Õ÷væD6GW&T&"ä–æ—D6öçG&öÇ2‚“°Ð Ð¢57G&–æurf–Fg&æÖRÂVFg&æÖS°Ð¢46öÕG#Ä”&6Tf–ÇFW#âf–D6F×ÂVD6F×°Ð Ð¢Õõf–DF—7æÖRÒôDBÓäF—7Æ”æÖU³Ó°Ð Ð¢–b‚Õõf–DF—7æÖRä—4V×G’‚’’°Ð¢–b‚7&VFTf–ÇFW"†Õõf–DF—7æÖRÂgf–D6F×Âf–Fg&æÖR’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó“c°Ð¢ÐÐ¢ÐÐ Ð¢ÕôVDF—7æÖRÒôDBÓäF—7Æ”æÖU³Ó°Ð Ð¢–b‚ÕôVDF—7æÖRä—4V×G’‚’’°Ð¢–b‚7&VFTf–ÇFW"†ÕôVDF—7æÖRÂgVD6F×ÂVFg&æÖR’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó“c°Ð¢ÐÐ¢ÐÐ Ð¢–b‚f–D6F×bbVD6F×’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó“ƒ°Ð¢ÐÐ Ð¢Õ÷4t"ÒçVÆÇG#°Ð¢Õ÷f–D6ÒçVÆÇG#°Ð¢Õ÷VD6ÒçVÆÇG#°Ð Ð¢–b„d”ÄTB†Õ÷4t"ä6ô7&VFT–ç7Fæ6R„4Å4”Eô6GW&Tw&„'V–ÆFW#"’’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õó““°Ð¢ÐÐ Ð¢…$U5TÅB‡#°Ð Ð¢Õ÷4t"Óå6WDf–ÇFW&w&‚†Õ÷t"“°Ð Ð¢–b‡f–D6F×’°Ð¢–b„d”ÄTB†‡"ÒÕ÷t"ÓäFDf–ÇFW"‡f–D6F×Âf–Fg&æÖR’’’°Ð¢F‡&÷r…T”åB””E5ô4EU$UôU%$õ%õd”Eôd”ÅDU#°Ð¢ÐÐ Ð¢Õ÷f–D6Òf–D6F×°Ð Ð¢–b‚VD6F×’°Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uô–çFW&ÆVfVBÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe446’’Ð¢bbd”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uõf–FVòÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe446’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F66GW&R"’“°Ð¢ÐÐ Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•õ$Ud”UrÂdÔTD”E•Uô–çFW&ÆVfVBÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe45&Wb’’Ð¢bbd”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•õ$Ud”UrÂdÔTD”E•Uõf–FVòÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe45&Wb’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F66GW&R"’“°Ð¢ÐÐ Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•UôVF–òÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Ô42’’Ð¢bbd”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•õ$Ud”UrÂdÔTD”E•UôVF–òÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Ô42’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F6"’“°Ð¢ÒVÇ6R°Ð¢Õ÷VD6ÒÕ÷f–D6°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uõf–FVòÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe446’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F66GW&R"’“°Ð¢ÐÐ Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uõf–FVòÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õe45&Wb’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F66GW&R"’“°Ð¢ÐÐ¢ÐÐ Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚dÄôôµõU5E$TÕôôäÅ’ÂçVÆÇG"ÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷Õ„&"’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Ô7&÷76&"–çFW&f6Rv2f÷VæEÆâ"’“°Ð¢ÐÐ Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚dÄôôµõU5E$TÕôôäÅ’ÂçVÆÇG"ÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷ÕGVæW"’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”ÕEeGVæW"–çFW&f6Rv2f÷VæEÆâ"’“°Ð¢ÐÐ¢òòDôDó¢–æ—BÕ÷Õ„& Ð Ð¢–b†Õ÷ÕGVæW"’²òòÆöB6fVB6†ææVÀÐ¢Õ÷ÕGVæW"ÓçWEô6÷VçG'”6öFR„g„vWD‚’ÓävWE&öf–ÆT–çB…õB‚$6GW&R"’ÂõB‚$6÷VçG'’"’Â’“°Ð Ð¢–çBf6†ææVÂÒôDBÓçf6†ææVÃ°Ð¢–b‡f6†ææVÂÂ’°Ð¢f6†ææVÂÒg„vWD‚’ÓävWE&öf–ÆT–çB…õB‚$6GW&UÅÂ"’²57G&–ær†Õõf–DF—7æÖR’ÂõB‚$6†ææVÂ"’ÂÓ“°Ð¢ÐÐ¢–b‡f6†ææVÂãÒ’°Ð¢ôf–ÇFW%7FFRg2Ò7FFUõ7F÷VC°Ð¢Õ÷Ô2ÓävWE7FFRƒÂfg2“°Ð¢–b†g2ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅW6R‡G'VR“°Ð¢ÐÐ¢Õ÷ÕGVæW"ÓçWEô6†ææVÂ‡f6†ææVÂÂÕETäU%õ5T$4„åôDTdTÅBÂÕETäU%õ5T$4„åôDTdTÅB“°Ð¢–b†g2ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅ'Vâ‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b‡VD6F×’°Ð¢–b„d”ÄTB†‡"ÒÕ÷t"ÓäFDf–ÇFW"‡VD6F×Â57G&–æur†VFg&æÖR’’’’°Ð¢F‡&÷r…T”åB””E5ô4EU$UôU%$õ%ôTEôd”ÅDU#°Ð¢ÐÐ Ð¢Õ÷VD6ÒVD6F×°Ð Ð¢–b„d”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•UôVF–òÂÕ÷VD6Â””Eõeô$u2‚fÕ÷Ô42’’Ð¢bbd”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•õ$Ud”UrÂdÔTD”E•UôVF–òÂÕ÷VD6Â””Eõeô$u2‚fÕ÷Ô42’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”Õ7G&VÔ6öæf–r–çFW&f6Rf÷"f–F6"’“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚†Õ÷f–D6ÇÂÕ÷VD6’’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õóƒ°Ð¢ÐÐ Ð¢ôDBÓçF—FÆRäÆöE7G&–ær„”E5ô4EU$UôÄ•dR“°Ð Ð¢6WEÆ–&6´ÖöFR…ÕôäÄôuô4EU$R“°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Vä7W7FöÖ—¦Tw&‚‚Ð§°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÒÕôd”ÄRbbvWEÆ–&6´ÖöFR‚’ÒÕôEdB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢6ÆVäw&‚‚“°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢–b†Õ÷4bbg„vWD6WGF–æw2‚’ä—4•5$WFôÆöDVæ&ÆVB‚’’°Ð¢FEFW‡E75F‡'Tf–ÇFW"‚“°Ð¢ÐÐ¢ÐÐ Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢6öç7B5&VæFW&W'56WGF–æw2b"Ò2æÕõ&VæFW&W'56WGF–æw3°Ð¢–b‡"æÕôGe&VæE6WG2æ%7–æ6‡&öæ—¦Uf–FVòbb2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5õ5”ä2’°Ð¢…$U5TÅB‡"Ò5ôô³°Ð¢Õ÷&Vd6Æö6²ÒDT%TuôäUr57–æ46Æö6´f–ÇFW"†çVÆÇG"Âf‡"“°Ð Ð¢–b…5T44TTDTB†‡"’bb5T44TTDTB†Õ÷t"ÓäFDf–ÇFW"†Õ÷&Vd6Æö6²ÂÂ%7–æ46Æö6²f–ÇFW""’’’°Ð¢46öÕ•G#Ä•&VfW&Væ6T6Æö6³â&Vd6Æö6²ÒÕ÷&Vd6Æö6³°Ð¢46öÕ•G#Ä”ÖVF–f–ÇFW#âÖVF–f–ÇFW"ÒÕ÷t#°Ð Ð¢–b‡&Vd6Æö6²bbÖVF–f–ÇFW"’°Ð¢dU$”e’…5T44TTDTB†ÖVF–f–ÇFW"Óå6WE7–æ56÷W&6R‡&Vd6Æö6²’’“°Ð¢ÖVF–f–ÇFW"ÒçVÆÇG#°Ð¢&Vd6Æö6²ÒçVÆÇG#°Ð Ð¢dU$”e’…5T44TTDTB†Õ÷&Vd6Æö6²ÓåVW'”–çFW&f6R„””Eõeô$u2‚fÕ÷7–æ46Æö6²’’’“°Ð¢46öÕ•G#Ä•7–æ46Æö6´Gf—6W#âGf—6W"ÒÕ÷4°Ð¢–b‡Gf—6W"’°Ð¢dU$”e’…5T44TTDTB‡Gf—6W"ÓäGf—6U7–æ46Æö6²†Õ÷7–æ46Æö6²’’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢–b†Õ÷Ee3"’°Ð¢–b‚Õ÷7V$6Æö6²’°Ð¢Õ÷7V$6Æö6²ÒDT%TuôäUr57V$6Æö6³°Ð¢ÐÐ¢Õ÷Ee3"ÓäGf—6U7V$6Æö6²†Õ÷7V$6Æö6²“°Ð¢ÐÐ¢ÐÐ Ð¢6ÆVäw&‚‚“°Ð§ÐÐ Ð¤56—¦R4Ö–äg&ÖS£¤÷Vå6WGWvWEf–FVõ6—¦R‚Ð§°Ð¢56—¦Rg2Ò56—¦RƒÃ“°Ð¢ÕödVF–ôöæÇ’ÒG'VS°Ð Ð¢–b†Õ÷ÔedD2’²òòUe Ð¢ÕödVF–ôöæÇ’ÒfÇ6S°Ð¢Õ÷ÔedD2ÓävWDæF—fUf–FVõ6—¦R‚gg2ÂçVÆÇG"“°Ð¢ÒVÇ6R–b†Õ÷4’°Ð¢g2ÒÕ÷4ÓävWEf–FVõ6—¦R†fÇ6R“°Ð¢–b‡g2æ7‚âbbg2æ7’â’°Ð¢ÕödVF–ôöæÇ’ÒfÇ6S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b„46öÕ•G#Ä”&6–5f–FVóâ%bÒÕ÷t"’°Ð¢%bÓävWEf–FVõ6—¦R‚gg2æ7‚Âgg2æ7’“°Ð¢–b‡g2æ7‚âbbg2æ7’â’°Ð¢ÕödVF–ôöæÇ’ÒfÇ6S°Ð¢ÐÐ¢ÐÐ¢–b†ÕödVF–ôöæÇ’bbÕ÷er’°Ð¢ÆöærÅf—6–&ÆS°Ð¢–b…5T44TTDTB†Õ÷erÓævWEõf—6–&ÆR‚fÅf—6–&ÆR’’’°Ð¢Õ÷erÓævWEõv–GF‚‚gg2æ7‚“°Ð¢Õ÷erÓævWEô†V–v‡B‚gg2æ7’“°Ð¢–b‡g2æ7‚âbbg2æ7’â’°Ð¢ÕödVF–ôöæÇ’ÒfÇ6S°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&âg3°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGWf–FVò‚Ð§°Ð¢4WFôÆö6²v‚fÆö6´w&„66W72“°Ð¢6–bDT%TpÐ¢54U%B†Æö6´w&„66W72æÕöÆö6´6÷VçBÓÒ“°Ð¢6VæF–`Ð Ð¢56—¦Rg2Ò÷Vå6WGWvWEf–FVõ6—¦R‚“°Ð¢–b†Õöe6†ö6·vfTw&‚’°Ð¢ÕödVF–ôöæÇ’ÒfÇ6S°Ð¢ÐÐ Ð¢Õ÷erÓçWEô÷væW"‚„ô…täB–Õ÷f–FVõvæBÓæÕö…væB“°Ð¢Õ÷erÓçWEõv–æF÷u7G–ÆR…u5ô4„”ÄBÂu5ô4Ä•4”$Ä”äu2Âu5ô4Ä•4„”ÄE$Tâ“°Ð¢Õ÷erÓçWEôÖW76vTG&–â‚„ô…täB–Õ÷f–FVõvæBÓæÕö…væB“°Ð Ð¢f÷"„5væB¢væBÒÕ÷f–FVõvæBÓävWEv–æF÷r„uuô4„”ÄB“²væC²væBÒvæBÓävWDæW‡Ev–æF÷r‚’’°Ð¢òòâÆWG2tÕõ4UD5U%4õ"F‡&÷Vv‚†æ÷BæVVFVB2öbæ÷rÐ¢òò"âÆÆ÷w24Ö÷W6S£¤7W'6÷$öåv–æF÷r‚’Fòv÷&²v—F‚Õ÷f–FVõvæ@Ð¢væBÓäVæ&ÆUv–æF÷r„dÅ4R“°Ð¢ÐÐ Ð¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢Õ÷eu÷&Wf–WrÓçWEô÷væW"‚„ô…täB–Õ÷væE&Uf–WrävWEf–FVô…täB‚’“°Ð¢Õ÷eu÷&Wf–WrÓçWEõv–æF÷u7G–ÆR…u5ô4„”ÄBÂu5ô4Ä•4”$Ä”äu2Âu5ô4Ä•4„”ÄE$Tâ“°Ð¢ÐÐ Ð¢–b†ÕödVF–ôöæÇ’’°Ð¢–b„†4FVF–6FVDe5f–FVõv–æF÷r‚’bbg„vWD6WGF–æw2‚’æ$gVÆÇ67&VVå6W&FT6öçG&öÇ2’²òôFVF–6FTe5v–æF÷rÆÆ÷vVBf÷"VF–ðÐ¢Õ÷FVF–6FVDe5f–FVõvæBÓäFW7G&÷•v–æF÷r‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚ÕödVF–ôöæÇ’bbÕöe6†ö6·vfTw&‚’°Ð¢Õ÷7FGW6&%f–FVõ6—¦Räf÷&ÖB…õB‚"VG‚VB"’Âg2æ7‚Âg2æ7’“°Ð¢WFFTE…d7FGW2‚“°Ð¢ÐÐ§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGWVF–ò‚Ð§°Ð¢Õ÷$ÓçWEõföÇVÖR†Õ÷væEFööÄ&"åföÇVÖR“°Ð Ð¢òòd•„ÔPÐ¢–çB&Ææ6RÒg„vWD6WGF–æw2‚’æä&Ææ6S°Ð Ð¢–çB6–vâÒ&Ææ6RâòÓ¢²òòÓ¢–çfW'B6–vâf÷"Ö÷&R&–v‡B6†ææVÀÐ¢–b†&Ææ6RâÓbb&Ææ6RÂ’°Ð¢&Ææ6RÒ6–vâ¢†–çB’ƒ¢#¢ÆösƒÒ'2†&Ææ6R’òãb’“°Ð¢ÒVÇ6R°Ð¢&Ææ6RÒ6–vâ¢‚Ó“²òòÓ¢öæÇ’ÆVgBÂ¢öæÇ’&–v‡@Ð¢ÐÐ Ð¢Õ÷$ÓçWEô&Ææ6R†&Ææ6R“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGW6GW&T&"‚Ð§°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôäÄôuô4EU$R’°Ð¢–b†Õ÷f–D6bbÕ÷Õe446’°Ð¢46öÕ•G#Ä”Õfgt6GW&TF–Æöw3âfgt4BÒÕ÷f–D6°Ð Ð¢–b‚Õ÷Õ„&"bbfgt4B’°Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WGWf–FVô6öçG&öÇ2†Õõf–DF—7æÖRÂÕ÷Õe446Âfgt4B“°Ð¢ÒVÇ6R°Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WGWf–FVô6öçG&öÇ2†Õõf–DF—7æÖRÂÕ÷Õe446ÂÕ÷Õ„&"ÂÕ÷ÕGVæW"“°Ð¢ÐÐ¢ÐÐ Ð¢–b†Õ÷VD6bbÕ÷Ô42’°Ð¢4–çFW&f6T'&“Ä”ÔVF–ô–çWDÖ—†W#âÔ”Ó°Ð Ð¢&Vv–äVçVÕ–ç2†Õ÷VD6ÂUÂ–â’°Ð¢–b„46öÕ•G#Ä”ÔVF–ô–çWDÖ—†W#â”ÒÒ–â’°Ð¢Ô”ÒäFB‡”Ò“°Ð¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WGWVF–ô6öçG&öÇ2†ÕôVDF—7æÖRÂÕ÷Ô42ÂÔ”Ò“°Ð¢ÐÐ Ð¢'V–ÆDw&…f–FVôVF–ò€Ð¢Õ÷væD6GW&T&"æÕö6FÆræÕöef–E&Wf–WrÂfÇ6RÀÐ¢Õ÷væD6GW&T&"æÕö6FÆræÕödVE&Wf–WrÂfÇ6R“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGW–æfô&"†&ööÂ$6ÆV"ò£ÒG'VR¢òÐ§°Ð¢&ööÂ%&V6Æ4Æ–÷WBÒfÇ6S°Ð Ð¢–b†$6ÆV"’°Ð¢Õ÷væD–æfô&"å&VÖ÷fTÆÄÆ–æW2‚“°Ð¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢46öÔ%5E"'7G#°Ð¢57G&–ærF—FÆRÂWF†÷"Â6÷—&–v‡BÂ&F–ærÂFW67&—F–öã°Ð¢–b†Õ÷ÔÔ5³Ò’°Ð¢f÷"†6öç7BWFòbÔÔ2¢Õ÷ÔÔ2’°Ð¢–b‡ÔÔ2’°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEõF—FÆR‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢F—FÆRÒ'7G"æÕ÷7G#°Ð¢F—FÆRåG&–Ò‚“°Ð¢ÐÐ¢'7G"äV×G’‚“°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEôWF†÷$æÖR‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢WF†÷"Ò'7G"æÕ÷7G#°Ð¢ÐÐ¢'7G"äV×G’‚“°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEô6÷—&–v‡B‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢6÷—&–v‡BÒ'7G"æÕ÷7G#°Ð¢ÐÐ¢'7G"äV×G’‚“°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEõ&F–ær‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢&F–ærÒ'7G"æÕ÷7G#°Ð¢ÐÐ¢'7G"äV×G’‚“°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEôFW67&—F–öâ‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢–b†'7G"äÆVæwF‚‚’ÂS"’°Ð¢FW67&—F–öâÒ'7G"æÕ÷7G#°Ð¢ÒVÇ6R–b†'7G"æÕ÷7G%³ÒÒÂw²r’°Ð¢FW67&—F–öâÒ57G&–ær†'7G"æÕ÷7G"’äÆVgBƒS“°Ð¢ÐÐ¢ÐÐ¢'7G"äV×G’‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õD•DÄR’ÂF—FÆR“°Ð¢WFFT6†FW$–ä–æfô&"‚“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôUD„õ"’ÂWF†÷"“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ô4õ•$”t…B’Â6÷—&–v‡B“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õ$D”är’Â&F–ær“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôDU45$•D”ôâ’ÂFW67&—F–öâ“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢57G&–ær–æfò…õB‚rÒr’“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôDôÔ”â’Â–æfò“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôÄô4D”ôâ’Â–æfò“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õd”DTò’Â–æfò“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôTD”ò’Â–æfò“°Ð¢%&V6Æ4Æ–÷WBÃÒÕ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õ5T%D•DÄU2’Â–æfò“°Ð¢ÐÐ Ð¢–b†%&V6Æ4Æ–÷WB’°Ð¢&V6Æ4Æ–÷WB‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFT6†FW$–ä–æfô&"‚Ð§°Ð¢57G&–ær6†FW#°Ð¢–b†Õ÷4"’°Ð¢Etõ$BGt6†6÷VçBÒÕ÷4"Óä6†vWD6÷VçB‚“°Ð¢–b†Gt6†6÷VçB’°Ð¢$TdU$Tä4UõD”ÔR'Dæ÷s°Ð¢Õ÷Õ2ÓävWD7W'&VçE÷6—F–öâ‚g'Dæ÷r“°Ð Ð¢–b†Õ÷4"’°Ð¢46öÔ%5E"'7G#°Ð¢Æöær7W'&VçD6†ÒÕ÷4"Óä6†Æöö·W‚g'Dæ÷rÂf'7G"“°Ð¢–b†'7G"äÆVæwF‚‚’’°Ð¢6†FW"äf÷&ÖB…õB‚"W2‚VÆBòVÇR’"’Â'7G"æÕ÷7G"Â7FC£¦Ö‚ƒÂÂ7W'&VçD6†²Â’ÂGt6†6÷VçB“°Ð¢ÒVÇ6R°Ð¢6†FW"äf÷&ÖB…õB‚"VÆBòVÇR"’Â7W'&VçD6†²ÂGt6†6÷VçB“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ô4„DU"’Â6†FW"’’°Ð¢&V6Æ4Æ–÷WB‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGW7FG4&"‚Ð§°Ð¢Õ÷væE7FG4&"å&VÖ÷fTÆÄÆ–æW2‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢57G&–ær–æfò…õB‚rÒr’“°Ð¢&ööÂ$f÷VæD”&—E&FT–æfòÒfÇ6S°Ð Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢–b‚Õ÷’°Ð¢Õ÷Ò$c°Ð¢ÐÐ¢–b‚Õ÷$’’°Ð¢Õ÷$’Ò$c°Ð¢ÐÐ¢–b‚$f÷VæD”&—E&FT–æfò’°Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢–b„46öÕ•G#Ä”&—E&FT–æfóâ%$’Ò–â’°Ð¢$f÷VæD”&—E&FT–æfòÒG'VS°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð¢ÐÐ¢–b†Õ÷bbÕ÷$’bb$f÷VæD”&—E&FT–æfò’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢–b†Õ÷’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5ôuôe$ÔU$DR’Â–æfò“°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5ôuôe$ÔU2’Â–æfò“°Ð¢–b‡2æ”E5f–FVõ&VæFW&W%G—RÒd”E$äEEôE5ôÔEe"bb2æ”E5f–FVõ&VæFW&W%G—RÒd”E$äEEôE5ôUe"bb2æ”E5f–FVõ&VæFW&W%G—RÒd”E$äEEôE5õ5”ä2’°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5õ5DE4$%õ5”ä5ôôde4UB’Â–æfò“°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5õ5DE4$%ô¤•EDU"’Â–æfò“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5õ5DE4$%õÄ”$4µõ$DR’Â–æfò“°Ð¢ÐÐ¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5õ5DE4$%õ4”täÂ’Â–æfò“°Ð¢ÐÐ¢–b†Õ÷$’’°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5ôuô%TddU%2’Â–æfò“°Ð¢ÐÐ¢–b†$f÷VæD”&—E&FT–æfò’°Ð¢Õ÷væE7FG4&"å6WDÆ–æR…7G%&W2„”E5õ5DE4$%ô$•E$DR’Â–æfò“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6†V6µ6VÆV7FVDVF–õ7G&VÒ‚Ð§°Ð¢–b†Õöd7W7FöÔw&‚’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–çBä6†ææVÇ2Ò°Ð¢–çBVF–÷7G&VÖ6÷VçBÒ°Ð¢T”åBVF–ö&—FÖ–BÒ”D%ôTD”õE•UôäôTD”ó°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÓ°Ð Ð¢–b†Õ÷VF–õ7v—F6†W%52’°Ð¢Etõ$B57G&V×2Ò°Ð¢–b…5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä6÷VçB‚f57G&V×2’’bb57G&V×2â’°Ð¢Ä4”BÆ6–BÒ°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢–b…5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢–b†Gtw&÷WÓÒ’°Ð¢–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒVF–÷7G&VÖ6÷VçC°Ð¢ä6†ææVÇ2ÒWFFU6VÆV7FVDVF–õ7G&VÔ–æfò†ÕöÆöFVDVF–õG&6´–æFW‚Â×BÂÆ6–B“°Ð¢ÐÐ¢VF–÷7G&VÖ6÷VçB²³°Ð¢ÐÐ¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†VF–÷7G&VÖ6÷VçBÓÒbbÕ÷7Æ—GFW%52’°Ð¢Etõ$B57G&V×2Ò°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW%52Óä6÷VçB‚f57G&V×2’’bb57G&V×2â’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW%52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢–b†Gtw&÷WÓÒ’°Ð¢–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒVF–÷7G&VÖ6÷VçC°Ð¢ä6†ææVÇ2ÒWFFU6VÆV7FVDVF–õ7G&VÔ–æfò†ÕöÆöFVDVF–õG&6´–æFW‚Â×BÂÆ6–B“°Ð¢ÐÐ¢VF–÷7G&VÖ6÷VçB²³°Ð¢ÐÐ¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†VF–÷7G&VÖ6÷VçBÓÒbbÕ÷7Æ—GFW$GV%52’°Ð¢Etõ$B57G&V×2Ò°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW$GV%52Óä6÷VçB‚f57G&V×2’’bb57G&V×2â’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW$GV%52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢–b†Gtw&÷WÓÒ’°Ð¢–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒVF–÷7G&VÖ6÷VçC°Ð¢ä6†ææVÇ2ÒWFFU6VÆV7FVDVF–õ7G&VÔ–æfò†ÕöÆöFVDVF–õG&6´–æFW‚Â×BÂÆ6–B“°Ð¢ÐÐ¢VF–÷7G&VÖ6÷VçB²³°Ð¢ÐÐ¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†VF–÷7G&VÖ6÷VçBÓÒbbÕ÷VF–õ7v—F6†W%52’²òòfÆÆ&6°Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢46öÕ•G#Ä”&6–4VF–óâ$Ò$c²òò–×ÆVÖVçFVB'’VF–ò&VæFW&W'0Ð¢&ööÂæ÷G&VæFW&W"ÒfÇ6S°Ð Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢–b…5ôô²ÓÒÕ÷t"Óä—5–äF—&V7F–öâ‡–âÂ”äD•%ô”åUB’bb5ôô²ÓÒÕ÷t"Óä—5–ä6öææV7FVB‡–â’’°Ð¢ÕôÔTD”õE•R×C°Ð¢–b…5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢–b†×BæÖ¦÷'G—RÓÒÔTD”E•UôVF–ò’°Ð¢æ÷G&VæFW&W"Ò$°Ð¢VF–÷7G&VÖ6÷VçBÒ°Ð¢ä6†ææVÇ2ÒWFFU6VÆV7FVDVF–õ7G&VÔ–æfò‚ÓÂf×BÂÓ“°Ð¢'&V³°Ð¢ÒVÇ6R–b†×BæÖ¦÷'G—RÓÒÔTD”E•UôÖ–F’’°Ð¢æ÷G&VæFW&W"ÒG'VS°Ð¢VF–÷7G&VÖ6÷VçBÒ°Ð¢ä6†ææVÇ2ÒWFFU6VÆV7FVDVF–õ7G&VÔ–æfò‚ÓÂf×BÂÓ“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð Ð¢–b†ä6†ææVÇ2âbbæ÷G&VæFW&W"’²òò&VfW"VF–òFV6öFW"&÷fR&VæFW&W Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð¢ÐÐ Ð¢–b†VF–÷7G&VÖ6÷VçBÓÒ’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÓ°Ð¢WFFU6VÆV7FVDVF–õ7G&VÔ–æfò‚ÓÂçVÆÇG"ÂÓ“°Ð¢ÐÐ Ð¢–b†ä6†ææVÇ2ãÒ"’°Ð¢VF–ö&—FÖ–BÒ”D%ôTD”õE•Uõ5DU$Tó°Ð¢ÒVÇ6R–b†ä6†ææVÇ2ÓÒ’°Ð¢VF–ö&—FÖ–BÒ”D%ôTD”õE•UôÔôäó°Ð¢ÐÐ¢Õ÷væE7FGW4&"å6WE7FGW4&—FÖ†VF–ö&—FÖ–B“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6†V6µ6VÆV7FVEf–FVõ7G&VÒ‚Ð§°Ð¢–b†Õöd7W7FöÔw&‚’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b†ÕödVF–ôöæÇ’’°Ð¢Õ÷7FGW6&%f–FVôf÷&ÖBäV×G’‚“°Ð¢ÐÐ Ð¢57G&–ærf63°Ð¢òòf–æBf–FVò÷WGWB–âöbF†R6÷W&6Rf–ÇFW"÷"7Æ—GFW Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢&ööÂ7Æ—GFW"Ò†6Ç6–BÓÒuT”EôÄe7Æ—GFW%6÷W&6RÇÂ6Ç6–BÓÒuT”EôÄe7Æ—GFW"“°Ð¢òòöæÇ’&ö6W72f–ÇFW'2F†BÖ–v‡B&R7Æ—GFW'0Ð¢–b‡7Æ—GFW"ÇÂ6Ç6–BÒõ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’bb6Ç6–BÒuT”EôÄef–FVòbb6Ç6–BÒuT”EôÄdVF–ò’°Ð¢–çB–çWE÷–ç2Ò°Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢”åôD•$T5D”ôâF—#°Ð¢4ÖVF–G—TW‚×C°Ð¢–b…5T44TTDTB‡–âÓåVW'”F—&V7F–öâ‚fF—"’’bb5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢–b†F—"ÓÒ”äD•%ôõUEUB’°Ð¢–b†×BæÖ¦÷'G—RÓÒÔTD”E•Uõf–FVò’°Ð¢vWEf–FVôf÷&ÖDæÖTg&öÔÖVF–G—R†×Bç7V'G—RÂf62“°Ð¢–b‡7Æ—GFW"’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢–çWE÷–ç2²³°Ð¢7Æ—GFW"Ò†×BæÖ¦÷'G—RÓÒÔTD”E•Uõ7G&VÒ“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð Ð¢–b‚†–çWE÷–ç2ÓÒÇÂ7Æ—GFW"’bbf62ä—4V×G’‚’’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢–b‚f62ä—4V×G’‚’’°Ð¢Õ÷7FGW6&%f–FVôf÷&ÖBÒf63°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGW7FGW4&"‚Ð§°Ð¢Õ÷væE7FGW4&"å6†÷uF–ÖW"‡G'VR“°Ð Ð¢6†V6µ6VÆV7FVEf–FVõ7G&VÒ‚“°Ð¢6†V6µ6VÆV7FVDVF–õ7G&VÒ‚“°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¤÷Vå6WGWv–æF÷uF—FÆR†&ööÂ&W6WBò£ÒfÇ6R¢òÐ§°Ð¢57G&–ærF—FÆR…7G%&W2„”E%ôÔ”äe$ÔR’“°Ð¢6–fFVbÕ4„5ôÄ•DPÐ¢F—FÆR³ÒõB‚"Æ—FR"“°Ð¢6VæF–`Ð Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–çB’Ò2æ•F—FÆT&%FW‡E7G–ÆS°Ð Ð¢–b‚&W6WBbb†’ÓÒÇÂ’ÓÒ’’°Ð¢òòF†W&R—2æòF‚–â6GW&RÖöFPÐ¢–b„—5Æ–&6´6GW&TÖöFR‚’’°Ð¢F—FÆRÒvWD6GW&UF—FÆR‚“°Ð¢ÒVÇ6R–b†’ÓÒ’²òò6†÷rf–ÆVæÖR÷"F—FÆPÐ¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢F—FÆRÒvWD&W7EF—FÆR‡2æeF—FÆT&%FW‡EF—FÆR“°Ð¢&ööÂ†5÷F—FÆRÒF—FÆRä—4V×G’‚“°Ð Ð¢57G&–æurfâÒvWDf–ÆTæÖR‚“°Ð Ð¢–b††5÷F—FÆRbb—4æÖU6–Ö–Æ"‡F—FÆRÂfâ’’2äÕ%Rå6WD7W'&VçEF—FÆR‡F—FÆR“°Ð Ð¢–b‚†5÷F—FÆR’°Ð¢F—FÆRÒfã°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢F—FÆRÒõB‚$EdB"“°Ð¢57G&–ærFƒ°Ð¢TÄôärÆVâÒ°Ð¢–b†Õ÷EdD’bb5T44TTDTB†Õ÷EdD’ÓävWDEdDF—&V7F÷'’‡F‚ävWD'VffW%6WDÆVæwF‚„Ô…õD‚’ÂÔ…õD‚ÂfÆVâ’’bbÆVâ’°Ð¢F‚å&VÆV6T'VffW"‚“°Ð¢–b‡F‚äf–æB…õB‚%ÅÅd”DTõõE2"’’ÓÒ"’°Ð¢F—FÆRäVæDf÷&ÖB…õB‚"ÒW2"’ÂvWDG&—fTÆ&VÂ„5F‚‡F‚’’ävWE7G&–ær‚’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÒVÇ6R²òò6†÷rgVÆÂF€Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢F—FÆRÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖUF—FÆR‚“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢F—FÆRÒõB‚$EdB"“°Ð¢TÄôärÆVâÒ°Ð¢–b†Õ÷EdD’’°Ð¢dU$”e’…5T44TTDTB†Õ÷EdD’ÓävWDEdDF—&V7F÷'’‡F—FÆRävWD'VffW%6WDÆVæwF‚„Ô…õD‚’ÂÔ…õD‚ÂfÆVâ’’“°Ð¢F—FÆRå&VÆV6T'VffW"‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢6WEv–æF÷uFW‡B‡F—FÆR“°Ð¢ÕôÆ6Bå6WDÖVF–F—FÆR‡F—FÆR“°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð¦–çB4Ö–äg&ÖS£¥6WGWVF–õ7G&V×2‚Ð§°Ð¢&ööÂ$—57Æ—GFW"ÒfÇ6S°Ð¢–çBFW6—&VEG&6´–æFW‚ÒÕöÆöFVDVF–õG&6´–æFWƒ°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÓ°Ð¢ÕöVF–õG&6´6÷VçBÒ°Ð Ð¢46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ52ÒÕ÷VF–õ7v—F6†W%53°Ð¢–b‚52’°Ð¢$—57Æ—GFW"ÒG'VS°Ð¢52ÒÕ÷7Æ—GFW%53°Ð¢ÐÐ Ð¢Etõ$B57G&V×2Ò°Ð¢–b‡52bb5T44TTDTB‡52Óä6÷VçB‚f57G&V×2’’’°Ð¢–b†57G&V×2â’°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢4FÄ'&“Ä57G&–æsâÆæw3°Ð¢–çBE÷2Ò°Ð¢57G&–ærÆærÒ2ç7G$VF–÷4ÆæwVvT÷&FW"åFö¶Væ—¦R…õB‚"Ã²"’ÂE÷2“°Ð¢v†–ÆR‡E÷2ÒÓ’°Ð¢ÆæräÖ¶TÆ÷vW"‚“°Ð¢Ææw2äFB†Æær“°Ð¢òòG'’FòÖF6‚F†RgVÆÂÆæwVvR–b÷76–&ÆPÐ¢ÆærÒ•4ôÆæs£¤•4óc3•…FôÆæwVvR„57G&–æt†Æær’“°Ð¢–b‚Æærä—4V×G’‚’’°Ð¢Ææw2äFB†ÆæräÖ¶TÆ÷vW"‚’“°Ð¢ÐÐ¢ÆærÒ2ç7G$VF–÷4ÆæwVvT÷&FW"åFö¶Væ—¦R…õB‚"Ã²"’ÂE÷2“°Ð¢ÐÐ Ð¢–çB6VÆV7FVBÒÓÂ–BÒ°Ð¢–çBÖ‡&F–ærÒÓ°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢t4„"¢æÖRÒçVÆÇG#°Ð¢46öÕG#Ä•Væ¶æ÷vãâö&¦V7C°Ð¢–b„d”ÄTB‡52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂgæÖRÂgö&¦V7BÂçVÆÇG"’’’°Ð¢6öçF–çVS°Ð¢ÐÐ¢57G&–æræÖR‡æÖR“°Ð¢6õF6´ÖVÔg&VR‡æÖR“°Ð Ð¢–b†Gtw&÷WÒ’°Ð¢54U%B†$—57Æ—GFW"“°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢ÕöVF–õG&6´6÷VçB²³°Ð Ð¢–çB&F–ærÒ°Ð¢òò–bF†RG&6²—26öçG&öÆÆVB'’7Æ—GFW"æB—6âwB6VÆV7FVBB7Æ—GFW"ÆWfVÀÐ¢–b‚†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’’°Ð¢&ööÂ%6¶—G&6³°Ð Ð¢òò–bF†R7Æ—GFW"—2F†R–çFW&æÂÄb7Æ—GFW"æBæòÆæwVvR&VfW&Væ6W0Ð¢òò†fR&VVâ6WBB7Æ—GFW"ÆWfVÂÂvR6â÷fW'&–FR—G26†ö–6R6fVÇÐ¢46öÕ•G#Ä”&6Tf–ÇFW#â$bÒ$—57Æ—GFW"ò52¢&V–çFW'&WEö67CÄ”&6Tf–ÇFW"£â‡ö&¦V7Bç“°Ð¢–b‡$bbb4dtf–ÇFW$Äc£¤—4–çFW&æÄ–ç7Fæ6R‡$b’’°Ð¢%6¶—G&6²ÒfÇ6S°Ð¢–b„46öÕ•G#Ä”Äde6WGF–æw3âÄde6WGF–æw2Ò$b’°Ð¢Åu5E"Ææu&Vg2ÒçVÆÇG#°Ð¢–b…5T44TTDTB‡Äde6WGF–æw2ÓävWE&VfW'&VDÆæwVvW2‚fÆæu&Vg2’’bbÆæu&Vg2bbv76ÆVâ†Ææu&Vg2’’°Ð¢%6¶—G&6²ÒG'VS°Ð¢ÐÐ¢6õF6´ÖVÔg&VR†Ææu&Vg2“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢%6¶—G&6²Ò2æ$ÆÆ÷t÷fW'&–F–ætW‡FW&æÅ7Æ—GFW$6†ö–6S°Ð¢ÐÐ Ð¢–b†%6¶—G&6²’°Ð¢–B²³°Ð¢6öçF–çVS°Ð¢ÐÐ¢ÒVÇ6R–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢òòv—fR6VÆV7FVBG&6²6Æ–v‡FÇ’†–v†W"&F–æpÐ¢&F–ær³Ò°Ð¢òòvWBFWF–Ç2öb7W'&VçFÇ’6VÆV7FVBG&6°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÕöVF–õG&6´6÷VçBÒ°Ð¢WFFU6VÆV7FVDVF–õ7G&VÔ–æfò†ÕöÆöFVDVF–õG&6´–æFW‚Â×BÂÆ6–B“°Ð¢ÐÐ Ð¢FVÆWFTÖVF–G—R‡×B“°Ð Ð¢æÖRåG&–Ò‚“°Ð¢æÖRäÖ¶TÆ÷vW"‚“°Ð Ð¢f÷"‡6—¦U÷B¢Ò²¢ÂÆæw2ävWD6÷VçB‚“²¢²²’°Ð¢–çBçVÒÒ÷G7Fö’†Ææw5¶¥Ò’Ò°Ð¢–b†çVÒãÒ’²òòF†—2—2G&6²çVÖ&W Ð¢–b†–BÒçVÒ’°Ð¢6öçF–çVS²òòæ÷BÖF6†V@Ð¢ÐÐ¢ÒVÇ6R²òòF†—2—2Æær7G&–æpÐ¢–çBÆVâÒÆæw5¶¥ÒävWDÆVæwF‚‚“°Ð¢–b†æÖRäÆVgB†ÆVâ’ÒÆæw5¶¥ÒbbæÖRäf–æB…õB‚%²"’²Ææw5¶¥Ò’Â’°Ð¢6öçF–çVS²òòæ÷BÖF6†V@Ð¢ÐÐ¢ÐÐ¢&F–ær³Òb¢–çB†Ææw2ävWD6÷VçB‚’Ò¢“°Ð¢'&V³°Ð¢ÐÐ¢–b†æÖRäf–æB…õB‚%¶FVfVÇBÆf÷&6VEÒ"’’ÒÓ’²òòf÷"Äb7Æ—GFW Ð¢&F–ær³ÒB²#°Ð¢ÐÐ¢–b†æÖRäf–æB…õB‚%¶f÷&6VEÒ"’’ÒÓ’°Ð¢&F–ær³Ò#°Ð¢ÐÐ¢–b†æÖRäf–æB…õB‚%¶FVfVÇEÒ"’’ÒÓ’°Ð¢&F–ær³ÒC°Ð¢ÐÐ Ð¢–b‡&F–ærâÖ‡&F–ær’°Ð¢Ö‡&F–ærÒ&F–æs°Ð¢6VÆV7FVBÒ–C°Ð¢ÐÐ Ð¢–B²³°Ð¢ÐÐ Ð¢–b†FW6—&VEG&6´–æFW‚ãÒbbFW6—&VEG&6´–æFW‚ÂÕöVF–õG&6´6÷VçB’°Ð¢6VÆV7FVBÒFW6—&VEG&6´–æFWƒ°Ð¢ÐÐ¢&WGW&âÕöVF–õG&6´6÷VçBâò6VÆV7FVB²$—57Æ—GFW"¢Ó°Ð¢ÒVÇ6R–b†57G&V×2ÓÒ’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢–b…5T44TTDTB‡52Óä–æfòƒÂg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢–b†Gtw&÷WÓÒbb†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚Ò°Ð¢ÕöVF–õG&6´6÷VçBÒ°Ð¢WFFU6VÆV7FVDVF–õ7G&VÔ–æfò†ÕöÆöFVDVF–õG&6´–æFW‚Â×BÂÆ6–B“°Ð¢ÐÐ¢FVÆWFTÖVF–G—R‡×B“°Ð¢&WGW&âÓ²òòæòæVVBFò6VÆV7B7V6–f–2G&6°Ð¢ÐÐ¢Ò Ð¢ÐÐ Ð¢&WGW&âÓ°Ð§ÐÐ Ð¦&ööÂÖF6…7V'G&6µv—F„•4ôÆær„57G&–ærbFæÖRÂ6öç7B•4ôÆæuCÄ57G&–æsâbÂÐ§°Ð¢–çB°Ð Ð¢–b‚Âæ—6óc3“"ä—4V×G’‚’’°Ð¢ÒFæÖRäf–æB…õB‚%²"’²Âæ—6óc3“"²õB‚%Ò"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB…õB‚"â"’²Âæ—6óc3“"²õB‚"â"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ Ð¢–b‚Âæ—6óc3“ä—4V×G’‚’’°Ð¢ÒFæÖRäf–æB…õB‚%²"’²Âæ—6óc3“²õB‚%Ò"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB…õB‚"â"’²Âæ—6óc3“²õB‚"â"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB…õB‚%²"’²Âæ—6óc3“²õB‚"ÕÒ"’“²òòG'Væ6FVB$5CpÐ¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ Ð¢–b‚ÂææÖRä—4V×G’‚’’°Ð¢–b†ÂææÖRÓÒõB‚&öfb"’’°Ð¢&WGW&âFæÖRäf–æB…õB‚&æò7V'F—FÆW2"’’ãÒ°Ð¢ÐÐ Ð¢7FC£¦Æ—7CÄ57G&–æsâÆævÆ—7C°Ð¢–çBE÷2Ò°Ð¢57G&–ærÆærÒÂææÖRåFö¶Væ—¦R…õB‚#²"’ÂE÷2“°Ð¢v†–ÆR‡E÷2ÒÓ’°Ð¢ÆæräÖ¶TÆ÷vW"‚’åG&–ÔÆVgB‚“°Ð¢ÆævÆ—7BæV×Æ6Uö&6²†Æær“°Ð¢ÆærÒÂææÖRåFö¶Væ—¦R…õB‚#²"’ÂE÷2“°Ð¢ÐÐ Ð¢f÷"†WFòb7V'7G"¢ÆævÆ—7B’°Ð¢ÒFæÖRäf–æB…õB‚%ÇB"’²7V'7G"“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB…õB‚"â"’²7V'7G"²õB‚"â"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB…õB‚%²"’²7V'7G"²õB‚%Ò"’“°Ð¢–b‡â’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÒFæÖRäf–æB‡7V'7G"“°Ð¢–b‡ÓÒÇÂÓÒ2bbFæÖRäÆVgBƒ2’ÓÒõB‚'3¢"’’²òòB&Vv–âöbG&6¶æÖPÐ¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&âfÇ6S°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð¦–çB4Ö–äg&ÖS£¥6WGW7V'F—FÆU7G&V×2‚Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–çB6VÆV7FVBÒÓ°Ð Ð¢–b‚Õ÷7V%7G&V×2ä—4V×G’‚’’°Ð¢&ööÂ—5öW‡FW&æÂÒfÇ6S°Ð¢&ööÂW‡FW&æÅ&–÷&—G’ÒfÇ6S°Ð¢&ööÂ†5ööfeöÆærÒfÇ6S°Ð¢7FC£¦Æ—7CÄ•4ôÆæuCÄ57G&–æsãâÆæw3°Ð¢–çBE÷2Ò°Ð¢57G&–ærÆærÒ2ç7G%7V'F—FÆW4ÆæwVvT÷&FW"åFö¶Væ—¦R…õB‚"Ã²"’ÂE÷2“°Ð¢v†–ÆR‡E÷2ÒÓ’°Ð¢ÆæräÖ¶TÆ÷vW"‚“°Ð¢•4ôÆæuCÄ57G&–æsâÂÒ•4ôÆæuCÄ57G&–æsâ†ÆærÂÂ""ÂÂ""Â“°Ð Ð¢–b†ÆærÓÒõB‚&öfb"’’°Ð¢†5ööfeöÆærÒG'VS°Ð¢ÒVÇ6R–b†Ææräf–æB„ÂrÒr’ÓÒ"’°Ð¢òò$5CpÐ¢ÒVÇ6R°Ð¢ÂÒ•4ôÆæs£¤•4óc3•…Fô•4ôÆær„57G&–æt†Æær’“°Ð¢–b†ÂææÖRä—4V×G’‚’’²òòæ÷Bâ•4ò6öFPÐ¢ÂææÖRÒÆæs°Ð¢ÒVÇ6R°Ð¢ÂææÖRäÖ¶TÆ÷vW"‚“°Ð¢ÐÐ¢ÐÐ Ð¢Ææw2æV×Æ6Uö&6²†Â“°Ð Ð¢ÆærÒ2ç7G%7V'F—FÆW4ÆæwVvT÷&FW"åFö¶Væ—¦R…õB‚"Ã²"’ÂE÷2“°Ð¢ÐÐ Ð¢–çB’Ò°Ð¢–çBÖ‡&F–ærÒ°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢–b†Õ÷÷4f—'7DW‡E7V"ÓÒ÷2’°Ð¢—5öW‡FW&æÂÒG'VS°Ð¢W‡FW&æÅ&–÷&—G’Ò2æe&–÷&—F—¦TW‡FW&æÅ7V'F—FÆW3°Ð¢ÐÐ¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð¢46öÕG#Ä•7V%7G&VÓâ7V%7G&VÒÒ7V$–çWBç7V%7G&VÓ°Ð¢46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBç6÷W&6Tf–ÇFW#°Ð Ð¢&ööÂ$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6S°Ð¢òò–bF†R–çFW&æÂÄb7Æ—GFW"†2—G2÷vâÆæwVvR&VfW&Væ6W26WBÂvR6†ö÷6Ræ÷BFò÷fW'&–FR—G26†ö–6PÐ¢–b‡54bbb4dtf–ÇFW$Äc£¤—4–çFW&æÄ–ç7Fæ6R‡7V$–çWBç6÷W&6Tf–ÇFW"’’°Ð¢$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6RÒG'VS°Ð¢–b„46öÕ•G#Ä”Äde6WGF–æw3âÄde6WGF–æw2Ò7V$–çWBç6÷W&6Tf–ÇFW"’°Ð¢46öÔ†VG#Åt4„#âÆæu&Vg3°Ð¢Äe7V'F—FÆTÖöFR7V'F—FÆTÖöFRÒÄde6WGF–æw2ÓävWE7V'F—FÆTÖöFR‚“°Ð¢–b‚‚‚‡7V'F—FÆTÖöFRÓÒÄe7V'F—FÆTÖöFUôFVfVÇBbb5T44TTDTB‡Äde6WGF–æw2ÓävWE&VfW'&VE7V'F—FÆTÆæwVvW2‚gÆæu&Vg2’’Ð¢ÇÂ‡7V'F—FÆTÖöFRÓÒÄe7V'F—FÆTÖöFUôGfæ6VBbb5T44TTDTB‡Äde6WGF–æw2ÓävWDGfæ6VE7V'F—FÆT6öæf–r‚gÆæu&Vg2’’’Ð¢bbÆæu&Vg2bbv76ÆVâ‡Ææu&Vg2’Ð¢ÇÂ7V'F—FÆTÖöFRÓÒÄe7V'F—FÆTÖöFUôf÷&6VDöæÇ’ÇÂ7V'F—FÆTÖöFRÓÒÄe7V'F—FÆTÖöFUôæõ7V'2’°Ð¢$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6RÒfÇ6S°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6RÒ2æ$ÆÆ÷t÷fW'&–F–ætW‡FW&æÅ7Æ—GFW$6†ö–6S°Ð¢ÐÐ Ð¢–çB6÷VçBÒ°Ð¢–b‡54b’°Ð¢Etõ$B57G&V×3°Ð¢–b…5T44TTDTB‡54bÓä6÷VçB‚f57G&V×2’’’°Ð¢6÷VçBÒ†–çB–57G&V×3°Ð¢ÐÐ¢ÒVÇ6R°Ð¢6÷VçBÒ7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“°Ð¢ÐÐ Ð¢f÷"†–çB¢Ò²¢Â6÷VçC²¢²²’°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢Ä4”BÆ6–BÒ°Ð¢–çB&F–ærÒ°Ð¢–b‡54b’°Ð¢Etõ$BGtfÆw2ÂGtw&÷WÒ#°Ð¢54bÓä–æfò†¢ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂgæÖRÂçVÆÇG"ÂçVÆÇG"“°Ð¢–b†Gtw&÷WÒ"’²òò–bF†RG&6²—6âwB7V'F—FÆRG&6²ÂvR6¶——@Ð¢6öçF–çVS°Ð¢ÒVÇ6R–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢òòv—fR6Æ–v‡FÇ’†–v†W"&–÷&—G’FòF†RG&6²6VÆV7FVB'’7Æ—GFW"6òF†@Ð¢òòvRvöâwB÷fW'&–FR6VÆV7FVBG&6²–â66RÆÂ†fRF†R6ÖR&F–æràÐ¢&F–ær³Ò°Ð¢ÒVÇ6R–b‚$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6R’°Ð¢òò–bvR&VâwBÆÆ÷vVBFòÖöF–g’F†R7Æ—GFW"6†ö–6RæBF†R7W'&Vç@Ð¢òòG&6²—6âwBÇ&VG’6VÆV7FVBB7Æ—GFW"ÆWfVÂvRæVVBFò6¶——BàÐ¢’²³°Ð¢6öçF–çVS°Ð¢ÐÐ¢ÒVÇ6R°Ð¢7V%7G&VÒÓävWE7G&VÔ–æfò†¢ÂgæÖRÂfÆ6–B“°Ð¢ÐÐ¢57G&–æræÖR‡æÖR“°Ð¢æÖRåG&–Ò‚“°Ð¢æÖRäÖ¶TÆ÷vW"‚“°Ð Ð¢6—¦U÷B²Ò°Ð¢f÷"†6öç7BWFòbÂ¢Ææw2’°Ð¢–çBçVÒÒ÷G7Fö’†ÂææÖR’Ò°Ð¢–b†çVÒãÒ’²òòF†—2—2G&6²çVÖ&W Ð¢–b†’ÒçVÒ’°Ð¢²²³°Ð¢6öçF–çVS²òòæ÷BÖF6†V@Ð¢ÐÐ¢ÒVÇ6R²òòF†—2—2Æær7G&–æpÐ¢–b†Æ6–BÓÒÇÂÆ6–BÓÒÄ4”B‚Ó’ÇÂÆ6–BÒÂæÆ6–B’°Ð¢òòæòÄ4”BÖF6‚ÂæÇ—¦RG&6²æÖRf÷"ÆæwVvRÖF6€Ð¢–b‚ÖF6…7V'G&6µv—F„•4ôÆær†æÖRÂÂ’’°Ð¢²²³°Ð¢6öçF–çVS²òòæ÷BÖF6†V@Ð¢ÐÐ¢ÐÐ¢òòÄ4”BÖF6€Ð¢ÐÐ¢&F–ær³Òb¢–çB†Ææw2ç6—¦R‚’Ò²“°Ð¢'&V³°Ð¢ÐÐ Ð¢–b†—5öW‡FW&æÂ’°Ð¢–b‡&F–ærâ’°Ð¢–b†W‡FW&æÅ&–÷&—G’’°Ð¢&F–ær³Òb¢–çB†Ææw2ç6—¦R‚’²“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†Ææw2ç6—¦R‚’ÓÒÇÂæÖRäf–æB…õB‚%ÇB"’’ÓÒÓ’°Ð¢òòæò&VfW'&VBÆæwVvR÷"Væ¶æ÷vâ7V"ÆæwVvPÐ¢–b†W‡FW&æÅ&–÷&—G’’°Ð¢&F–ær³Òb¢–çB†Ææw2ç6—¦R‚’²“°Ð¢ÒVÇ6R°Ð¢&F–ærÒ°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢–b‡2æ%&VfW$FVfVÇDf÷&6VE7V'F—FÆW2’°Ð¢–b†æÖRäf–æB…õB‚%¶FVfVÇBÆf÷&6VEÒ"’’ÒÓ’²òòf÷"Äb7Æ—GFW Ð¢&F–ær³ÒB²#°Ð¢ÐÐ¢–b†æÖRäf–æB…õB‚%¶f÷&6VEÒ"’’ÒÓ’°Ð¢&F–ær³Ò#°Ð¢ÐÐ¢–b†æÖRäf–æB…õB‚%¶FVfVÇEÒ"’’ÒÓ’°Ð¢&F–ær³ÒC°Ð¢ÐÐ¢ÐÐ¢6–b Ð¢–b‡&F–ærÓÒbb$ÆÆ÷t÷fW'&–F–æu7Æ—GFW$6†ö–6RbbÆæw2ç6—¦R‚’ÓÒ’°Ð¢òòW6Rf—'7BVÖ&VFFVBG&6²2fÆÆ&6²–bF†W&R—2æò&VfW'&VBÆæwVvPÐ¢&F–ærÒ°Ð¢ÐÐ¢6VæF–`Ð¢ÐÐ Ð¢–b‡&F–ærâÖ‡&F–ær’°Ð¢Ö‡&F–ærÒ&F–æs°Ð¢6VÆV7FVBÒ“°Ð¢ÐÐ¢’²³°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b‡2ä—4•5$WFôÆöDVæ&ÆVB‚’bbÕödVF–ôöæÇ’’°Ð¢–b‡2æ$WFôF÷væÆöE7V'F—FÆW2bbÕ÷7V%7G&V×2ä—4V×G’‚’’°Ð¢Õ÷7V'F—FÆW5&÷f–FW'2Óå6V&6‚…E%TR“°Ð¢ÒVÇ6R–b†Õ÷væE7V'F—FÆW4F÷væÆöDF–Æörä—5v–æF÷uf—6–&ÆR‚’’°Ð¢Õ÷7V'F—FÆW5&÷f–FW'2Óå6V&6‚„dÅ4R“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&â6VÆV7FVC°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤÷VäÖVF–&—fFR„4WFõG#Ä÷VäÖVF–FFâôÔBÐ§°Ð¢54U%B„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôD”är“°Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–&—fFR‡F‡&VBVÇR’"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ Ð¢–b†Õ÷t"ÇÂÕô7F—fTw&„æ÷F–g”Wd6öFRÓÒT5õU4TBÇÂvWDÆöE7FFR‚’ÒÔÅ3£¤ÄôD”ärÇÂÕôöä6Æ÷6Uö6ÆÆVB’°Ð¢54U%B†fÇ6R“°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢6VæF–`Ð¢ÐÐ Ð¢ÕöefÆ–DEdD÷VâÒfÇ6S°Ð¢Õö”FVe&÷FF–öâÒ°Ð Ð¢÷Väf–ÆTFF¢f–ÆTFFÒG–æÖ–5ö67CÄ÷Väf–ÆTFF£â‡ôÔBæÕ÷“°Ð¢÷VäEdDFF¢EdDFFÒG–æÖ–5ö67CÄ÷VäEdDFF£â‡ôÔBæÕ÷“°Ð¢÷VäFWf–6TFF¢FWf–6TFFÒG–æÖ–5ö67CÄ÷VäFWf–6TFF£â‡ôÔBæÕ÷“°Ð¢54U%B‡f–ÆTFFÇÂEdDFFÇÂFWf–6TFF“°Ð Ð¢Õ÷42ÒçVÆÇG#°Ð¢Õ÷4"ÒçVÆÇG#°Ð¢Õ÷4ÒçVÆÇG#°Ð¢Õ÷dÕ%t2ÒçVÆÇG#°Ð¢Õ÷dÕ$Ô2ÒçVÆÇG#°Ð¢Õ÷ÔedD2ÒçVÆÇG#°Ð¢Õ÷dÔ"ÒçVÆÇG#°Ð¢Õ÷ÔedÔ"ÒçVÆÇG#°Ð¢Õ÷ÔeeÒçVÆÇG#°Ð¢Õ÷Õe$2ÒçVÆÇG#°Ð¢Õ÷Õe$’ÒçVÆÇG#°Ð¢Õ÷Õe%2ÒçVÆÇG#°Ð¢Õ÷Õe%5"ÒçVÆÇG#°Ð¢Õ÷Õe$drÒçVÆÇG#°Ð¢Õ÷ÕeDòÒçVÆÇG#°Ð¢Õ÷C4De42ÒçVÆÇG#°Ð¢Õ÷Äã#ÒçVÆÇG#°Ð¢Õ÷4%÷&Wf–WrÒçVÆÇG#°Ð¢Õ÷ÔedD5÷&Wf–WrÒçVÆÇG#°Ð¢Õ÷Ôee÷&Wf–WrÒçVÆÇG#°Ð¢Õ÷dÕ#”5÷&Wf–WrÒçVÆÇG#°Ð Ð¢6–fFVbôDT%TpÐ¢òòFV'VrG&6R6öFRÒ&Vv–àÐ¢òò6†V6²f÷"&Bò'Vvw’WFòÆöF–ærf–ÆR6öFPÐ¢–b‡f–ÆTFF’°Ð¢E$4R…õB‚"ÒÓâ4Ö–äg&ÖS£¤÷VäÖVF–&—fFRöâF‡&VC¢VÇUÆâ"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢õ4•D”ôâ÷2Òf–ÆTFFÓæfç2ävWD†VE÷6—F–öâ‚“°Ð¢T”åB–æFW‚Ò°Ð¢v†–ÆR‡÷2ÒçVÆÇG"’°Ð¢57G&–ærF‚Òf–ÆTFFÓæfç2ävWDæW‡B‡÷2“°Ð¢E$4R…õB‚%ÇGf–ÆTFFÓæfç5²WUÓ¢Ww5Æâ"’Â–æFW‚ÂF‚ävWE7G&–ær‚’“²òòWw2Òv–FR6†&7FW"7G&–ærÇv—0Ð¢–æFW‚²³°Ð¢ÐÐ¢ÐÐ¢òòFV'VrG&6R6öFRÒVæ@Ð¢6VæF–`Ð Ð¢57G&–ærW'#°Ð¢G'’°Ð¢WFò6†V6´&÷'FVBÒ²eÒ‚’°Ð¢–b†Õöd÷Væ–æt&÷'FVB’°Ð¢F‡&÷r…T”åB””E5ôuô$õ%DTC°Ð¢ÐÐ¢Ó°Ð Ð¢÷Vä7&VFTw&„ö&¦V7B‡ôÔB“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢–b‡f–ÆTFF’°Ð¢÷Väf–ÆR‡f–ÆTFF“°Ð¢ÒVÇ6R–b‡EdDFF’°Ð¢÷VäEdB‡EdDFF“°Ð¢ÒVÇ6R–b‡FWf–6TFF’°Ð¢–b‡2æ”FVfVÇD6GW&TFWf–6RÓÒ’°Ð¢…$U5TÅB‡"Ò÷Vä$Dw&‚‚“°Ð¢–b„d”ÄTB†‡"’’°Ð¢F‡&÷r…T”åB””E5ô4EU$UôU%$õ%ôDUd”4S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢÷Vä6GW&R‡FWf–6TFF“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢F‡&÷r…T”åB””E5ô”ådÄ”Eõ$Õ5ôU%$õ#°Ð¢ÐÐ Ð¢–b‚Õ÷t"’°Ð¢F‡&÷r…T”åB””E5ôÔ”äe$Õóƒƒ°Ð¢ÐÐ Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–&—fFRÒf–ÇFW"w&‚†2&VVâ7&VFVB"’“°Ð¢ÐÐ Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷4’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷4"’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷42’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÕ%t2’ÂdÅ4R“²òòÖ–v‡B†fR•dÕ$Ö—†W$&—FÖ’Â'WBæ÷B•dÕ%v–æF÷vÆW746öçG&öÃÐ¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÕ$Ô2’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÔ"’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷ÔedÔ"’ÂE%TR“°Ð Ð¢Õ÷Õe$2ÒÕ÷4°Ð¢Õ÷Õe$’ÒÕ÷4°Ð¢Õ÷Õe%2ÒÕ÷4°Ð¢Õ÷Õe%5"ÒÕ÷4°Ð¢Õ÷Õe$drÒÕ÷4°Ð¢Õ÷ÕeDòÒÕ÷4°Ð¢Õ÷C4De42ÒÕ÷4°Ð Ð¢6†V6´&÷'FVB‚“°Ð Ð¢6WGWdÕ#”6öÆ÷$6öçG&öÂ‚“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷ÔedD2’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷Ôee’ÂE%TR“°Ð¢–b†Õ÷ÔedD2’°Ð¢Õ÷ÔedD2Óå6WEf–FVõv–æF÷r†Õ÷f–FVõvæBÓæÕö…væB“°Ð¢ÐÐ Ð¢òò4ôÔÔTåDTBõUC¢FöW2æ÷Bv÷&²BF†—2Æö6F–öâÂæVVBFò6†ö÷6RF†R6÷'&V7BÖöFR„”Ôef–FVõ&ö6W76÷#£¥6WEf–FVõ&ö6W76÷$ÖöFRÐ¢òõ6WGWUe$6öÆ÷$6öçG&öÂ‚“°Ð Ð¢–b†Õö%W6U6VVµ&Wf–Wr’°Ð¢Õ÷t%÷&Wf–WrÓäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷ÔedD5÷&Wf–Wr’ÂE%TR“°Ð¢Õ÷t%÷&Wf–WrÓäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷Ôee÷&Wf–Wr’ÂE%TR“°Ð¢Õ÷t%÷&Wf–WrÓäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÕ#”5÷&Wf–Wr’ÂE%TR“°Ð¢Õ÷t%÷&Wf–WrÓäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷4%÷&Wf–Wr’ÂE%TR“°Ð Ð¢$T5Bw#°Ð¢Õ÷væE&Uf–WrävWEf–FVõ&V7B‚gw"“°Ð¢–b†Õ÷ÔedD5÷&Wf–Wr’°Ð¢Õ÷ÔedD5÷&Wf–WrÓå6WEf–FVõv–æF÷r†Õ÷væE&Uf–WrävWEf–FVô…täB‚’“°Ð¢Õ÷ÔedD5÷&Wf–WrÓå6WEf–FVõ÷6—F–öâ†çVÆÇG"Âgw"“°Ð¢ÐÐ¢–b†Õ÷4%÷&Wf–Wr’°Ð¢Õ÷4%÷&Wf–WrÓå6WE÷6—F–öâ‡w"Âw"“°Ð¢ÐÐ¢ÐÐ Ð¢–b†Õ÷Äã#’°Ð¢Õ÷Äã#Óå6WE6W'f–6U7FFR‡2æd6Æ÷6VD6F–öç2òÕôÃ#ô455DDUôöâ¢ÕôÃ#ô455DDUôöfb“°Ð¢ÐÐ Ð¢6†V6´&÷'FVB‚“°Ð Ð¢÷Vä7W7FöÖ—¦Tw&‚‚“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢÷Vå6WGWf–FVò‚“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢–b‡2æe6†÷tõ4BÇÂ2æe6†÷tFV'Vt–æfò’²òòf÷&6Rõ4Böâv†VâF†RFV'Vr7v—F6‚—2W6V@Ð¢Õôõ4Bå7F÷‚“°Ð Ð¢–b†Õ÷ÕeDò’°Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷ÕeDò“°Ð¢ÒVÇ6R–b†ÕödgVÆÅ67&VVâbbÕödVF–ôöæÇ’bbÕ÷42’²òòÕ5e Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷dÔ"ÂÕ÷ÔedÔ"ÂfÇ6R“°Ð¢ÒVÇ6R–b‚ÕödVF–ôöæÇ’bb—4C4DgVÆÅ67&VVäÖöFR‚’bb†Õ÷dÔ"ÇÂÕ÷ÔedÔ"’’°Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷dÔ"ÂÕ÷ÔedÔ"ÂG'VR“°Ð¢ÒVÇ6R°Ð¢Õôõ4Bå7F'B†Õ÷õ4EvæB“°Ð¢ÐÐ¢ÐÐ Ð¢÷Vå6WGWVF–ò‚“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRbbf–ÆTFF’°Ð¢6öç7B57G&–ærbfâÒf–ÆTFFÓæfç2ävWD†VB‚“°Ð¢òòFöâwBG'’Fò6fRf–ÆR÷6—F–öâ–b6÷W&6R—6âwB6VV¶&ÆPÐ¢$TdU$Tä4UõD”ÔR'E÷2Ò°Ð¢$TdU$Tä4UõD”ÔR'DGW"Ò°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÓ°Ð¢ÕöÆöFVE7V'F—FÆUG&6´–æFW‚ÒÓ°Ð Ð¢–b†Õ÷Õ2’°Ð¢Õ÷Õ2ÓävWDGW&F–öâ‚g'DGW"“°Ð¢ÐÐ Ð¢Õö%&VÖVÖ&W$f–ÆU÷2Ò2æd¶VW†—7F÷'’bb2æe&VÖVÖ&W$f–ÆU÷2bb'DGW"â‡2æ•&VÖVÖ&W%÷4f÷$ÆöævW%F†â¢“cB¢c“cB’bb‡2æ%&VÖVÖ&W%÷4f÷$VF–ôf–ÆW2ÇÂÕödVF–ôöæÇ’“°Ð Ð¢òò6WB7F'BF–ÖR'WB6VV²öæÇ’gFW"ÆÂf–ÆW2&RÆöFV@Ð¢–b‡f–ÆTFFÓç'E7F'Bâ’²òò6†V6²–bâW‡Æ–6—B7F'BF–ÖRv2v—fVàÐ¢'E÷2Òf–ÆTFFÓç'E7F'C°Ð¢ÐÐ¢–b‡f–ÆTFFÓæ%&WVB’²òò6†V6²–bâW‡Æ–6—Bö"&WVBF–ÖRv2v—fVàÐ¢%&WVBÒf–ÆTFFÓæ%&WVC°Ð¢ÐÐ Ð¢–b†Õ÷'E&VÆöE÷2ãÒ’°Ð¢–b†Õ÷'E&VÆöE÷2Â'DGW"’°Ð¢'E÷2ÒÕ÷'E&VÆöE÷3°Ð¢ÐÐ¢Õ÷'E&VÆöE÷2ÒÓ°Ð¢ÐÐ¢–b‡&VÆöD%&WVB’°Ð¢%&WVBÒ&VÆöD%&WVC°Ð¢&VÆöD%&WVBÒ%&WVB‚“°Ð¢ÐÐ Ð¢WFò¢Õ%RÒdg„vWD6WGF–æw2‚’äÕ%S°Ð¢–b‡Õ%RÓç&fUö'&’ävWD6÷VçB‚’’°Ð¢–b‚'E÷2bbÕö%&VÖVÖ&W$f–ÆU÷2’°Ð¢'E÷2ÒÕ%RÓävWD7W'&VçDf–ÆU÷6—F–öâ‚“°Ð¢–b‡'E÷2ãÒ'DGW"ÇÂ'DGW"Ò'E÷2ÂSÄÂ’°Ð¢'E÷2Ò°Ð¢ÐÐ¢ÐÐ¢–b‚%&WVBbb2æd¶VW†—7F÷'’bb2æe&VÖVÖ&W$f–ÆU÷2’°Ð¢%&WVBÒÕ%RÓävWD7W'&VçD%&WVB‚“°Ð¢ÐÐ¢–b‡2æd¶VW†—7F÷'’bb2æ%&VÖVÖ&W%G&6µ6VÆV7F–öâ’°Ð¢–b†ÕöÆöFVDVF–õG&6´–æFW‚ÓÒÓ’°Ð¢ÕöÆöFVDVF–õG&6´–æFW‚ÒÕ%RÓävWD7W'&VçDVF–õG&6²‚“°Ð¢ÐÐ¢–b†ÕöÆöFVE7V'F—FÆUG&6´–æFW‚ÓÒÓ’°Ð¢ÕöÆöFVE7V'F—FÆUG&6´–æFW‚ÒÕ%RÓävWD7W'&VçE7V'F—FÆUG&6²‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†%&WVBbb%&WVBç÷6—F–öä"â’°Ð¢òòfÆ–FFPÐ¢–b†%&WVBç÷6—F–öä"â'DGW"ÇÂ%&WVBç÷6—F–öäãÒ%&WVBç÷6—F–öä"’°Ð¢%&WVBÒ%&WVB‚“°Ð¢ÐÐ¢ÐÐ¢–b†%&WVB’°Ð¢Õ÷væE6VV´&"ä–çfÆ–FFR‚“°Ð¢ÐÐ Ð¢–b‡'E÷2bb'DGW"’°Ð¢Õ÷Õ2Óå6WE÷6—F–öç2‚g'E÷2ÂÕõ4TT´”äuô'6öÇWFU÷6—F–öæ–ærÂçVÆÇG"ÂÕõ4TT´”äuôæõ÷6—F–öæ–ær“°Ð¢ÐÐ Ð¢FVfVÇEf–FVôævÆRÒ°Ð¢–b†Õ÷e4bbb†Õ÷4"ÇÂÕ÷42ÇÂÕ÷VF–õ7v—F6†W%52’’°Ð¢46öÕ•G#Ä”&6Tf–ÇFW#â$bÒÕ÷e4c°Ð¢–b„vWD4Å4”B‡$b’ÓÒuT”EôÄe7Æ—GFW"ÇÂvWD4Å4”B‡$b’ÓÒuT”EôÄe7Æ—GFW%6÷W&6R’°Ð¢–b„46öÕ•G#Ä•&÷W'G”&sâ"Ò$b’°Ð¢46öÕf&–çBf#°Ð¢–b†Õ÷4"ÇÂÕ÷42’°Ð¢–b…5T44TTDTB‡"Óå&VB…õB‚'&÷FF–öâ"’Âgf"ÂçVÆÇG"’’bbf"çgBÓÒeEô%5E"’°Ð¢–çB&÷FFWfÇVRÒ÷wFö’‡f"æ'7G%fÂ“°Ð¢–b‡&÷FFWfÇVRÂ’°Ð¢&÷FFWfÇVR³Ò3c°Ð¢ÐÐ¢–b‡&÷FFWfÇVRÓÒ“ÇÂ&÷FFWfÇVRÓÒƒÇÂ&÷FFWfÇVRÓÒ#s’°Ð¢Õö”FVe&÷FF–öâÒ&÷FFWfÇVS°Ð¢–b†Õ÷42’°Ð¢Õ÷42Óå6WE&÷FF–öâ‡&÷FFWfÇVR“°Ð¢ÒVÇ6R°Ð¢Õ÷4"Óå6WDFVfVÇEf–FVôævÆR…fV7F÷"ƒÂÂfV7F÷#£¤FVuFõ&Bƒ3cÒ&÷FFWfÇVR’’“°Ð¢ÐÐ¢–b†Õ÷4%÷&Wf–Wr’°Ð¢FVfVÇEf–FVôævÆRÒ3cÒ&÷FFWfÇVS°Ð¢Õ÷4%÷&Wf–WrÓå6WDFVfVÇEf–FVôævÆR…fV7F÷"ƒÂÂfV7F÷#£¤FVuFõ&B†FVfVÇEf–FVôævÆR’’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢f"ä6ÆV"‚“°Ð¢ÐÐ¢–b†Õ÷VF–õ7v—F6†W%52’°Ð¢–b…5T44TTDTB‡"Óå&VB…õB‚'&WÆ–v–å÷G&6µöv–â"’Âgf"ÂçVÆÇG"’’bbf"çgBÓÒeEô%5E"’°Ð¢òòFôFó¢'6RfÇVRÂFBgVæ7F–öâFòVF–ò7v—F6†W"f–ÇFW"Fò6WB&WÆ–v–âfÇVRÂÇ’—B6–Ö–Æ"Fò&ö÷7BæB6¶—æ÷&ÖÆ—¦R†æB&VwVÆ"&ö÷7CòÐ¢f"ä6ÆV"‚“°Ð¢ÒVÇ6R–b…5T44TTDTB‡"Óå&VB…õB‚'&WÆ–v–åöÆ'VÕöv–â"’Âgf"ÂçVÆÇG"’’bbf"çgBÓÒeEô%5E"’°Ð¢f"ä6ÆV"‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢6†V6´&÷'FVB‚“°Ð Ð¢–b†Õ÷4bb2ä—4•5$WFôÆöDVæ&ÆVB‚’bbÕödVF–ôöæÇ’’°Ð¢–b‡2ædF—6&ÆT–çFW&æÅ7V'F—FÆW2’°Ð¢Õ÷7V%7G&V×2å&VÖ÷fTÆÂ‚“²òòæVVG2Fò&R&WÆ6VBv—F‚6öFRF†B6†V6·2f÷"f÷&6VB7V'F—FÆW2àÐ¢ÐÐ¢Õ÷÷4f—'7DW‡E7V"ÒçVÆÇG#°Ð¢–b‚ôÔBÓç7V'2ä—4V×G’‚’’°Ð¢õ4•D”ôâ÷2ÒôÔBÓç7V'2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢ÆöE7V'F—FÆR‡ôÔBÓç7V'2ävWDæW‡B‡÷2’ÂçVÆÇG"ÂG'VR“°Ð¢ÐÐ¢ÐÐ Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’bbÆ’æÕö%–÷WGV&TDÂbb2ç5”DÅ7V'5&VfW&Væ6Rä—4V×G’‚’’°Ð¢õ4•D”ôâ÷3"ÒÆ’æÕ÷–FÅ÷7V'2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷3"’°Ð¢5–÷WGV&TDÄ–ç7Fæ6S£¥”DÅ7V$–æfò–FÇ7V"ÒÆ’æÕ÷–FÅ÷7V'2ävWDæW‡B‡÷3"“°Ð¢–b‚–FÇ7V"æ—4WFöÖF–46F–öç2ÇÂ2æ%W6TWFöÖF–46F–öç2’°Ð¢ÆöE7V'F—FÆR‡–FÇ7V"“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢6†V6´&÷'FVB‚“°Ð Ð¢÷Vå6WGWv–æF÷uF—FÆR‚“°Ð¢6†V6´&÷'FVB‚“°Ð Ð¢–çBVG7FÓ²òòöfg6WB–âVF–òG&6²ÖVçRÂVF–õ7v—F6†W"FG2â$÷F–öç2"VçG'’&÷fRF†RVF–òG&6·0Ð¢VG7FÒÒ6WGWVF–õ7G&V×2‚“°Ð¢–b†VG7FÒãÒ’°Ð¢öåÆ”VF–ò„”EôTD”õõ5T$•DTÕõ5D%B²VG7FÒ“°Ð¢ÐÐ¢6†V6´&÷'FVB‚“°Ð Ð¢–çB7V'7FÓ°Ð¢–b†ÕöÆöFVE7V'F—FÆUG&6´–æFW‚ãÒbb—5fÆ–E7V'F—FÆU7G&VÒ†ÕöÆöFVE7V'F—FÆUG&6´–æFW‚’’°Ð¢7V'7FÒÒÕöÆöFVE7V'F—FÆUG&6´–æFWƒ°Ð¢ÒVÇ6R°Ð¢7V'7FÒÒ6WGW7V'F—FÆU7G&V×2‚“°Ð¢ÐÐ¢–b‡7V'7FÒãÒ’°Ð¢6WE7V'F—FÆR‡7V'7FÒ“°Ð¢ÐÐ¢6†V6´&÷'FVB‚“°Ð Ð¢òòÇ’öGV&FVÆ’6öÖÖæBÖÆ–æR7v—F6€Ð¢òòDôDó¢F†B6öÖÖæBÖÆ–æR7v—F6‚&ö&&Ç’æVVG2&Wf—6–öàÐ¢–b‡2ç'E6†–gBÒ’°Ð¢6WDVF–ôFVÆ’‡2ç'E6†–gB“°Ð¢2ç'E6†–gBÒ°Ð¢ÐÐ¢Ò6F6‚„Å5E5E"×6r’°Ð¢W'"Ò×6s°Ð¢Ò6F6‚„57G&–ærb×6r’°Ð¢W'"Ò×6s°Ð¢Ò6F6‚…T”åB×6r’°Ð¢W'"äÆöE7G&–ær†×6r“°Ð¢ÐÐ Ð¢–b†Õö%W6U6VVµ&Wf–WrbbÕ÷Ô5÷&Wf–Wr’°Ð¢Õ÷Ô5÷&Wf–WrÓåW6R‚“°Ð¢ÐÐ Ð¢Õö6Æ÷6–æv×6rÒW'#°Ð Ð¢WFòvWDÖW76vT&w2Ò²eÒ‚’°Ð¢u$ÒwÒf–ÆTFFòÕôd”ÄR¢EdDFFòÕôEdB¢FWf–6TFFò‡2æ”FVfVÇD6GW&TFWf–6RÓÒòÕôD”t•DÅô4EU$R¢ÕôäÄôuô4EU$R’¢ÕôäôäS°Ð¢54U%B‡wÒÕôäôäR“°Ð¢Å$ÒÇÒ„Å$Ò—ôÔBäFWF6‚‚“°Ð¢54U%B†Ç“°Ð¢&WGW&â7FC£¦Ö¶U÷—"‡wÂÇ“°Ð¢Ó°Ð Ð¢–b†W'"ä—4V×G’‚’’°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–&—fFRÒ6ö×ÆWFVB"’“°Ð¢ÐÐ¢WFò&w2ÒvWDÖW76vT&w2‚“°Ð¢–b‚Õö$÷VæVEF‡&÷Vv…F‡&VB’°Ð¢54U%B„vWD7W'&VçEF‡&VD–B‚’ÓÒg„vWD‚’ÓæÕöåF‡&VD”B“°Ð¢öäf–ÆU÷7D÷VæÖVF–†&w2æf—'7BÂ&w2ç6V6öæB“°Ð¢ÒVÇ6R°Ð¢÷7DÖW76vR…tÕõõ5DõTâÂ&w2æf—'7BÂ&w2ç6V6öæB“°Ð¢ÐÐ¢ÒVÇ6R–b‚Õöd÷Væ–æt&÷'FVB’°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–&—fFRÒf–ÇW&S¢W2"’ÂW'"“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢WFò&w2ÒvWDÖW76vT&w2‚“°Ð¢–b‚Õö$÷VæVEF‡&÷Vv…F‡&VB’°Ð¢54U%B„vWD7W'&VçEF‡&VD–B‚’ÓÒg„vWD‚’ÓæÕöåF‡&VD”B“°Ð¢öä÷VäÖVF–f–ÆVB†&w2æf—'7BÂ&w2ç6V6öæB“°Ð¢ÒVÇ6R°Ð¢÷7DÖW76vR…tÕôõTäd”ÄTBÂ&w2æf—'7BÂ&w2ç6V6öæB“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢Õö$÷VäÖVF–7F—fRÒfÇ6S°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–&—fFRÒ&÷'FVB"’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&âW'"ä—4V×G’‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6Æ÷6TÖVF–&—fFR‚Ð§°Ð¢54U%B„vWDÆöE7FFR‚’ÓÒÔÅ3£¤4Äõ4”är“°Ð Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–&—fFR‡F‡&VBVÇR’Ò7F'B"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢ÐÐ Ð¢TÄôätÄôärF3ÒvWEF–6´6÷VçCcB‚“°Ð Ð¢òò7F÷F†Rw&‚&Vf÷&R&VÆV6–ær—BàÐ¢òò7F÷–ær6â&Æö6²–æFVf–æ—FVÇ’öâ7GV6²6÷W&6Rf–ÇFW"†RærââVç&W7öç6—fRæWGv÷&²7G&VÒÐ¢òòF†Rw&‚v÷&¶W"F‡&VB6â&RWF–Æ—¦VBFò6F6‚7V6‚FVFÆö6·0Ð¢ÖVF–6öçG&öÅ7F÷‡G'VR“°Ð Ð¢Õô66†VDf–ÇFW%7FFRÒÓ°Ð Ð¢ÕödÆ—fUtÒÒfÇ6S°Ð¢ÕödVæDöe7G&VÒÒfÇ6S°Ð¢Õö$'VffW&–ærÒfÇ6S°Ð¢Õ÷'DGW&F–öä÷fW'&–FRÒÓ°Ð¢Õö%W6–ætE…dÒfÇ6S°Ð¢ÕöVF–õG&6´6÷VçBÒ°Ð¢&W6WDWFô6÷•7V'F—FÆR‚“°Ð Ð¢–b†Õ÷Ed%7FFR’°Ð¢Õ÷Ed%7FFRÓä¦ö–â‚“°Ð¢Õ÷Ed%7FFRÒçVÆÇG#°Ð¢ÐÐ¢Õ÷4"å&VÆV6R‚“°Ð Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢Õ÷7W'&VçE7V$–çWBÒ7V'F—FÆT–çWB†çVÆÇG"“°Ð¢Õ÷6V6öæF'•7V$–çWBÒ7V'F—FÆT–çWB†çVÆÇG"“°Ð¢Õ÷7V%7G&V×2å&VÖ÷fTÆÂ‚“°Ð¢ÕôW‡FW&æÅ7V'7G&V×2æ6ÆV"‚“°Ð¢ÐÐ¢Õ÷7V$6Æö6²å&VÆV6R‚“°Ð Ð¢Õôõ4Bå7F÷‚“°Ð Ð¢–b†Õ÷erbbÕ÷Õe%2’°Ð¢Õ÷erÓçWEô÷væW"„åTÄÂ“°Ð¢ÐÐ¢–b†Õ÷eu÷&Wf–Wr’°Ð¢Õ÷eu÷&Wf–WrÓçWEô÷væW"„åTÄÂ“°Ð¢ÐÐ Ð¢Õö$—4Õ5e$W†6ÇW6—fTÖöFRÒfÇ6S°Ð Ð¢òò”Õõ%DåC¢•dÕ%7W&f6TÆÆö6F÷$æ÷F–g’ô•dÕ%7W&f6TÆÆö6F÷$æ÷F–g“’†2Fò&R&VÆV6VB&Vf÷&RF†RdÕ"õdÕ#’Â÷F†W'v—6R—Bv–ÆÂ7&6‚–â&VÆV6R‚Ð¢Õ÷Õe$drå&VÆV6R‚“°Ð¢Õ÷Õe%5"å&VÆV6R‚“°Ð¢Õ÷Õe%2å&VÆV6R‚“°Ð¢Õ÷Õe$2å&VÆV6R‚“°Ð¢Õ÷Õe$’å&VÆV6R‚“°Ð¢Õ÷ÕeDòå&VÆV6R‚“°Ð¢Õ÷C4De42å&VÆV6R‚“°Ð¢Õ÷42å&VÆV6R‚“°Ð¢Õ÷4"å&VÆV6R‚“°Ð¢Õ÷4å&VÆV6R‚“°Ð¢Õ÷dÕ%t2å&VÆV6R‚“°Ð¢Õ÷dÕ$Ô2å&VÆV6R‚“°Ð¢Õ÷dÔ"å&VÆV6R‚“°Ð¢Õ÷ÔedÔ"å&VÆV6R‚“°Ð¢Õ÷Ôeeå&VÆV6R‚“°Ð¢Õ÷ÔedD2å&VÆV6R‚“°Ð¢Õ÷Äã#å&VÆV6R‚“°Ð¢Õ÷7–æ46Æö6²å&VÆV6R‚“°Ð Ð¢Õ÷Õ„&"å&VÆV6R‚“°Ð¢Õ÷ÔDbå&VÆV6R‚“°Ð¢Õ÷Õd46å&VÆV6R‚“°Ð¢Õ÷Õd5&Wbå&VÆV6R‚“°Ð¢Õ÷Õe446å&VÆV6R‚“°Ð¢Õ÷Õe45&Wbå&VÆV6R‚“°Ð¢Õ÷Ô42å&VÆV6R‚“°Ð¢Õ÷f–D6å&VÆV6R‚“°Ð¢Õ÷VD6å&VÆV6R‚“°Ð¢Õ÷ÕGVæW"å&VÆV6R‚“°Ð¢Õ÷4t"å&VÆV6R‚“°Ð Ð¢Õ÷EdD2å&VÆV6R‚“°Ð¢Õ÷EdD’å&VÆV6R‚“°Ð¢Õ÷Ôõå&VÆV6R‚“°Ð¢Õ÷$’å&VÆV6R‚“°Ð¢Õ÷å&VÆV6R‚“°Ð¢Õ÷e2å&VÆV6R‚“°Ð¢Õ÷Õ2å&VÆV6R‚“°Ð¢Õ÷$å&VÆV6R‚“°Ð¢Õ÷%bå&VÆV6R‚“°Ð¢Õ÷erå&VÆV6R‚“°Ð¢Õ÷ÔRå&VÆV6R‚“°Ð¢Õ÷Ô2å&VÆV6R‚“°Ð¢Õ÷e4bå&VÆV6R‚“°Ð¢Õ÷´d’å&VÆV6R‚“°Ð¢Õ÷Ôå2å&VÆV6R‚“°Ð¢Õ÷Ee2å&VÆV6R‚“°Ð¢Õ÷Ee3"å&VÆV6R‚“°Ð¢f÷"†WFòbÔÔ2¢Õ÷ÔÔ2’°Ð¢ÔÔ2å&VÆV6R‚“°Ð¢ÐÐ¢Õ÷VF–õ7v—F6†W%52å&VÆV6R‚“°Ð¢Õ÷7Æ—GFW%52å&VÆV6R‚“°Ð¢Õ÷7Æ—GFW$GV%52å&VÆV6R‚“°Ð¢f÷"†WFòb52¢Õ÷÷F†W%52’°Ð¢52å&VÆV6R‚“°Ð¢ÐÐ Ð¢E$4R…õB‚%&VÆV6–ærw&‚'V–ÆFW%Æâ"’“°Ð¢–b†Õ÷t"’°Ð¢Õ÷t"Óå&VÖ÷fTg&öÕ$õB‚“°Ð¢Õ÷t"å&VÆV6R‚“°Ð¢ÐÐ¢E$4R…õB‚%&VÆV6–ærw&‚'V–ÆFW"6ö×ÆWFUÆâ"’“°Ð Ð¢TÄôätÄôärF3"ÒvWEF–6´6÷VçCcB‚“°Ð Ð¢–b†Õ÷t%÷&Wf–Wr’°Ð¢E$4R…õB‚%&VÆV6–ær&Wf–Wrw&…Æâ"’“°Ð¢&VÆV6U&Wf–Wtw&‚‚“°Ð¢ÐÐ Ð¢Õ÷&÷bå&VÆV6R‚“°Ð Ð¢Õöd7W7FöÔw&‚ÒÕöe6†ö6·vfTw&‚ÒfÇ6S°Ð Ð¢ÕöÆ7DôÔBäg&VR‚“°Ð Ð –ÕôföçD–ç7FÆÆW"åVæ–ç7FÆÄföçG2‚“°Ð Ð¢TÄôätÄôärF32ÒvWEF–6´6÷VçCcB‚“°Ð Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–&—fFRÒ6ö×ÆWFRÒVÆÇV×2VÆÇV×2"’ÂF3"×F3ÂF32×F3"“°Ð¢ÒVÇ6R–b‡F32×F3ãÒ#’°Ð¢E$4R…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–&—fFRÒ6ö×ÆWFRÒVÆÇV×2VÆÇV×5Æâ"’ÂF3"ÒF3ÂF32ÒF3"“°Ð¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥v–ÆF6&Df–ÆU6V&6‚„57G&–ær6V&6‡7G"Â7FC£§6WCÄ57G&–ærÂ57G&–æuWF–Ç3£¤Æöv–6ÄÆW73âb&W7VÇG2Â&ööÂ&V7W'6UöF—'2Â7FC£¦ÖÄ57G&–ærÂTÄôätÄôäsâ¢7&VF–öåF–ÖW2Ð§°Ð¢W‡FVæDÖ…F„ÆVæwF„–dæVVFVB‡6V&6‡7G"“°Ð Ð¢57G&–ærF‚Ò6V&6‡7G#°Ð¢F‚å&WÆ6R‚ròrÂuÅÂr“°Ð¢–çBÒF‚å&WfW'6Tf–æB‚uÅÂr“°Ð¢–b‡Â’&WGW&âfÇ6S°Ð¢F‚ÒF‚äÆVgB‡²“°Ð Ð¢t”ã3%ôd”äEôDDf–æDFF°Ð¢¦W&ôÖVÖ÷'’‚ff–æDFFÂ6—¦Vöb…t”ã3%ôd”äEôDD’“°Ð¢„äDÄR‚Òf–æDf—'7Df–ÆR‡6V&6‡7G"Âff–æDFF“°Ð¢–b†‚Ò”ådÄ”Eô„äDÄUõdÅTR’°Ð¢57G&–ær6V&6…öW‡BÒ6V&6‡7G"äÖ–B‡6V&6‡7G"å&WfW'6Tf–æB‚râr’’äÖ¶TÆ÷vW"‚“°Ð¢&ööÂ÷F†W%öW‡BÒ‡6V&6…öW‡BÒõB‚"â¢"’“°Ð¢57G&–æur7W$W‡BÒ5F‚†Õ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‚’’ävWDW‡FVç6–öâ‚’äÖ¶TÆ÷vW"‚“°Ð Ð¢WFòFDf–ÆRÒ²eÒ†6öç7B57G&–ærbfâ’°Ð¢&W7VÇG2æ–ç6W'B†fâ“°Ð¢–b†7&VF–öåF–ÖW2’°Ð¢TÄ$tUô”åDTtU"gC°Ð¢gBäÆ÷u'BÒf–æDFFægD7&VF–öåF–ÖRæGtÆ÷tFFUF–ÖS°Ð¢gBä†–v…'BÒf–æDFFægD7&VF–öåF–ÖRæGt†–v„FFUF–ÖS°Ð¢‚¦7&VF–öåF–ÖW2•¶fåÒÒgBåVE'C°Ð¢ÐÐ¢Ó°Ð Ð¢Fò°Ð¢57G&–ærf–ÆVæÖRÒf–æDFFæ4f–ÆTæÖS°Ð Ð¢–b†f–æDFFæGtf–ÆTGG&–'WFW2bd”ÄUôEE$”%UDUôD•$T5Dõ%’’°Ð¢–b‡&V7W'6UöF—'2bb6V&6…öW‡BÓÒÂ"â¢"bbf–ÆVæÖRÒÂ"â"bbf–ÆVæÖRÒÂ"ââ"’°Ð¢v–ÆF6&Df–ÆU6V&6‚‡F‚²f–ÆVæÖR²Â%ÅÂ¢â¢"Â&W7VÇG2ÂG'VRÂ7&VF–öåF–ÖW2“°Ð¢ÐÐ¢6öçF–çVS°Ð¢ÐÐ Ð¢57G&–ærW‡BÒf–ÆVæÖRäÖ–B†f–ÆVæÖRå&WfW'6Tf–æB‚râr’’äÖ¶TÆ÷vW"‚“°Ð Ð¢–b„6å6¶—FôW‡B†W‡BÂ7W$W‡B’’°Ð¢ò¢Æ–Æ—7BæB7VRf–ÆW26†÷VÆB&R–væ÷&VBv†Vâ6V&6†–ærF—"f÷"Æ–&ÆRf–ÆW2¢ðÐ¢–b‚—5Æ–Æ—7Df–ÆTW‡B†W‡B’’°Ð¢FDf–ÆR‡F‚²f–ÆVæÖR“°Ð¢ÐÐ¢ÒVÇ6R–b†÷F†W%öW‡Bbb6V&6…öW‡BÓÒW‡B’°Ð¢FDf–ÆR‡F‚²f–ÆVæÖR“°Ð¢–b†W‡BÓÒõB‚"ç&""’’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢Òv†–ÆR„f–æDæW‡Df–ÆR†‚Âff–æDFF’“°Ð Ð¢f–æD6Æ÷6R†‚“°Ð¢ÐÐ Ð¢&WGW&â&W7VÇG2ç6—¦R‚’â°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥6V&6„–äF—"†&ööÂ$F—$f÷'v&BÂ&ööÂ$Æö÷ò£ÒfÇ6R¢òÐ§°Ð¢54U%B„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRÇÂ6å6¶—g&öÔ6Æ÷6VDf–ÆR‚’“°Ð Ð¢57G&–ærf–ÆVæÖS°Ð Ð¢WFòf–ÆTFFÒG–æÖ–5ö67CÄ÷Väf–ÆTFF£â†ÕöÆ7DôÔBæÕ÷“°Ð¢–b‚f–ÆTFFÇÂf–ÆTFFÓçF—FÆRÇÂf–ÆTFFÓçF—FÆRä—4V×G’‚’’°Ð¢–b„6å6¶—g&öÔ6Æ÷6VDf–ÆR‚’’°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’ÓÒ’°Ð¢f–ÆVæÖRÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWD†VB‚’æÕöfç2ävWD†VB‚“°Ð¢ÒVÇ6R°Ð¢f–ÆVæÖRÒÆ7D÷Väf–ÆS°Ð¢ÐÐ¢ÒVÇ6R°Ð¢54U%B„dÅ4R“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢f–ÆVæÖRÒf–ÆTFFÓçF—FÆS°Ð¢ÐÐ Ð¢–b…F…WF–Ç3£¤—5U$Â†f–ÆVæÖR’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–çBÒf–ÆVæÖRå&WfW'6Tf–æB…õB‚uÅÂr’“°Ð¢–b‡Â’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢6öç7B&ööÂ%6÷'D'”FFRÒg„vWD6WGF–æw2‚’æ$æW‡Df–ÆT–äföÆFW%6÷'D'”FFS°Ð Ð¢57G&–ærf–ÆVÖ6²Òf–ÆVæÖRäÆVgB‡²’²õB‚"¢â¢"“°Ð¢7FC£§6WCÄ57G&–ærÂ57G&–æuWF–Ç3£¤Æöv–6ÄÆW73âf–ÆVÆ—7C°Ð¢7FC£¦ÖÄ57G&–ærÂTÄôätÄôäsâ7&VF–öåF–ÖW3°Ð¢–b‚v–ÆF6&Df–ÆU6V&6‚†f–ÆVÖ6²Âf–ÆVÆ—7BÂfÇ6RÂ%6÷'D'”FFRòf7&VF–öåF–ÖW2¢çVÆÇG"’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢òòvRÖ¶R7W&RF†BF†R7W'&VçFÇ’÷VæVBf–ÆR—2FFVBFòF†RÆ—7@Ð¢òòWfVâ–b—Bw2öbâVæ¶æ÷vâf÷&ÖBàÐ¢WFò7W'&VçBÒf–ÆVÆ—7Bæ–ç6W'B†f–ÆVæÖR’æf—'7C°Ð Ð¢–b†f–ÆVÆ—7Bç6—¦R‚’Â"bb5F‚†f–ÆVæÖR’äf–ÆTW†—7G2‚’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢57G&–æræW‡Ff–ÆS°Ð Ð¢–b†%6÷'D'”FFR’°Ð¢7FC£§fV7F÷#Ç7FC£§—#ÅTÄôätÄôärÂ57G&–æsãâF–ÖVÆ—7C°Ð¢F–ÖVÆ—7Bç&W6W'fR†f–ÆVÆ—7Bç6—¦R‚’“°Ð¢f÷"†6öç7B57G&–ærbf–ÆR¢f–ÆVÆ—7B’°Ð¢TÄôätÄôärF–ÖRÒ°Ð¢WFò—BÒ7&VF–öåF–ÖW2æf–æB†f–ÆR“°Ð¢–b†—BÒ7&VF–öåF–ÖW2æVæB‚’’°Ð¢F–ÖRÒ—BÓç6V6öæC°Ð¢ÒVÇ6R²òòF†R7W'&VçFÇ’÷VæVBf–ÆRÂv†Vâ—Bv2æ÷B'BöbF†R6V&6‚&W7VÇG0Ð¢t”ã3%ôd”ÄUôEE$”%UDUôDDfC°Ð¢–b„vWDf–ÆTGG&–'WFW4W‚†f–ÆRÂvWDf–ÆTW„–æfõ7FæF&BÂffB’’°Ð¢TÄ$tUô”åDTtU"gC°Ð¢gBäÆ÷u'BÒfBægD7&VF–öåF–ÖRæGtÆ÷tFFUF–ÖS°Ð¢gBä†–v…'BÒfBægD7&VF–öåF–ÖRæGt†–v„FFUF–ÖS°Ð¢F–ÖRÒgBåVE'C°Ð¢ÐÐ¢ÐÐ¢F–ÖVÆ—7BæV×Æ6Uö&6²‡F–ÖRÂf–ÆR“°Ð¢ÐÐ¢òò7F&ÆR6÷'B¶VW2F‚÷&FW"f÷"–FVçF–6ÂF–ÖW0Ð¢7FC£§7F&ÆU÷6÷'B‡F–ÖVÆ—7Bæ&Vv–â‚’ÂF–ÖVÆ—7BæVæB‚’ÂµÒ†6öç7BWFòbÆ‡2Â6öç7BWFòb&‡2’°Ð¢&WGW&âÆ‡2æf—'7BÂ&‡2æf—'7C°Ð¢Ò“°Ð Ð¢6—¦U÷B–G‚Ò°Ð¢f÷"‡6—¦U÷B’Ò²’ÂF–ÖVÆ—7Bç6—¦R‚“²’²²’°Ð¢–b‡F–ÖVÆ—7E¶•Òç6V6öæBÓÒf–ÆVæÖR’°Ð¢–G‚Ò“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢–b†$F—$f÷'v&B’°Ð¢–b†–G‚²ÂF–ÖVÆ—7Bç6—¦R‚’’°Ð¢–G‚²³°Ð¢ÒVÇ6R–b†$Æö÷’°Ð¢–G‚Ò°Ð¢ÒVÇ6R°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†–G‚â’°Ð¢–G‚ÒÓ°Ð¢ÒVÇ6R–b†$Æö÷’°Ð¢–G‚ÒF–ÖVÆ—7Bç6—¦R‚’Ò°Ð¢ÒVÇ6R°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ¢æW‡Ff–ÆRÒF–ÖVÆ—7E¶–G…Òç6V6öæC°Ð¢ÒVÇ6R°Ð¢–b†$F—$f÷'v&B’°Ð¢7W'&VçB²³°Ð¢–b†7W'&VçBÓÒf–ÆVÆ—7BæVæB‚’’°Ð¢–b†$Æö÷’°Ð¢7W'&VçBÒf–ÆVÆ—7Bæ&Vv–â‚“°Ð¢ÒVÇ6R°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢–b†7W'&VçBÓÒf–ÆVÆ—7Bæ&Vv–â‚’’°Ð¢–b†$Æö÷’°Ð¢7W'&VçBÒf–ÆVÆ—7BæVæB‚“°Ð¢ÒVÇ6R°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ¢7W'&VçBÒÓ°Ð¢ÐÐ¢æW‡Ff–ÆRÒ¦7W'&VçC°Ð¢ÐÐ Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð¢6ÂäFD†VB†æW‡Ff–ÆR“°Ð¢Õ÷væEÆ–Æ—7D&"ä÷Vâ‡6ÂÂfÇ6R“°Ð Ð¢&WGW&âG'VS°Ð§ÐÐ Ð§7FF–26öç7B–çBE45ôd•%5Eô4„ääTÂÒ#°Ð§7FF–26öç7B–çBE45ôd•%5EõT„eô4„ääTÂÒC°Ð§7FF–26öç7B–çBE45ôÄ5EõT„eô4„ääTÂÒS°Ð§7FF–26öç7B–çBE45õ$D”õô5E$ôäôÕ•ô4„ääTÂÒ3s°Ð Ð¢òò6VçG&Rg&WVVæ7’–â´‡¢öbU2E42FW'&W7G&–Â$b6†ææVÂÂ÷"fÇ6R–bF†PÐ¢òò6†ææVÂçVÖ&W"—2æ÷BöæRF†B6'&–W2'&öF67BàÐ¢òðÐ¢òòF†RÆâ—2FVÆ–&W&FVÇ’Æöö·W&F†W"F†â&—F†ÖWF–2Â&V6W6R—B—2æ÷BÐ¢òòVæ–f÷&Ò&7FW"â7FW–ær'’&æGv–GF‚Òv†–6‚—2v†BEd"66âFöW2Âæ@Ð¢òòv†BF†—266âW6VBFòFòf÷"WfW'’7FæF&BÒ—26÷'&V7BöæÇ’v—F†–â&æC Ð¢òòF†W&R—2Ô‡¢7FW&WGvVVâ6†ææVÇ2BæBRÂF†RdÒ'&öF67B&æB6—G0Ð¢òò&WGvVVâbæBrÂæB#cÔ‡¢6W&FR2g&öÒBâbÔ‡¢7vVWF†W&Vf÷&PÐ¢òòÆæG2öfbÖ6†ææVÂg&öÒ6†ææVÂRöçv&G2æBv7FW26öÖRf÷'G’GVæ–æpÐ¢òòGFV×G27&÷76–ærF†Rv&VÆ÷rT„bàÐ§7FF–2&ööÂvWDE446†ææVÄg&WVVæ7’†–çBä6†ææVÂÂTÄôärbVÄg&WVVæ7’Ð§°Ð¢òòd„bÆ÷rƒ"Ób’æBd„b†–v‚ƒrÓ2’&R—'&VwVÆ"æB&RÆ—7FVB÷WBàÐ¢7FF–26öç7B7G'V7B²–çBä6†ææVÃ²TÄôärVÄg&WVVæ7“²Òd„d6†ææVÇ5µÒÒ°Ð¢²"ÂSsÒÂ²2Âc3ÒÂ²BÂc“ÒÀÐ¢²RÂs“ÒÂ²bÂƒSÒÀÐ¢²rÂssÒÂ²‚Âƒ3ÒÂ²’Âƒ“ÒÂ²Â“SÒÀÐ¢²Â#ÒÂ²"Â#sÒÂ²2Â#3ÒÀÐ¢Ó°Ð Ð¢f÷"†6öç7BWFòb6†ææVÂ¢d„d6†ææVÇ2’°Ð¢–b†6†ææVÂæä6†ææVÂÓÒä6†ææVÂ’°Ð¢VÄg&WVVæ7’Ò6†ææVÂçVÄg&WVVæ7“°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ Ð¢òòT„b—2&VwVÆ"bÔ‡¢&7FW"7F'F–ærB6†ææVÂBöâCs2Ô‡¢àÐ¢òò6†ææVÂ3r—2&W6W'fVBv÷&ÆGv–FRf÷"&F–ò7G&öæö×’æBæWfW"6'&–W2Ð¢òò'&öF67BÂ6ò&V6V—fW'26¶——Bâ&÷fR6†ææVÂ3bF†R&æBv2&V76–væV@Ð¢òòFòÖö&–ÆRW6R'’F†R#r&W6²Â'WBöÆFW"&V6÷&F–æw2Ö’7F–ÆÂ6—@Ð¢òòF†W&RÂ6òF†RÆâ'Vç2Fò6†ææVÂSàÐ¢–b†ä6†ææVÂãÒE45ôd•%5EõT„eô4„ääTÂbbä6†ææVÂÃÒE45ôÄ5EõT„eô4„ääTÂbbä6†ææVÂÒE45õ$D”õô5E$ôäôÕ•ô4„ääTÂ’°Ð¢VÄg&WVVæ7’ÒCs3²†ä6†ææVÂÒE45ôd•%5EõT„eô4„ääTÂ’¢c°Ð¢&WGW&âG'VS°Ð¢ÐÐ Ð¢&WGW&âfÇ6S°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤FõGVæW%66â…GVæW%66äFF¢E4BÐ§°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢46öÕ•G#Ä”$DGVæW#âGVâÒÕ÷t#°Ð¢–b‡GVâ’°Ð¢&ööÂv57F÷VBÒfÇ6S°Ð¢–b„vWDÖVF–7FFR‚’ÓÒ7FFUõ7F÷VB’°Ð¢6WD6†ææVÂ‚Ó“°Ð¢ÖVF–6öçG&öÅ'Vâ‚“°Ð¢v57F÷VBÒG'VS°Ð¢ÐÐ Ð¢$ôôÄTâ%&W6VçC°Ð¢$ôôÄTâ$Æö6¶VC°Ð¢ÄôärÄF%7G&VæwF‚Ò°Ð¢ÄôärÅW&6VçEVÆ—G’Ò°Ð¢–çBäöfg6WBÒE4BÓäöfg6WBò2¢°Ð¢ÄôärÄöfg6WG5³5ÒÒ³ÂE4BÓäöfg6WBÂ×E4BÓäöfg6WGÓ°Ð¢Õö%7F÷GVæW%66âÒfÇ6S°Ð¢GVâÓå66âƒÂÂÂåTÄÂ“²òò6ÆV"Ö0Ð Ð¢òòv÷&²÷WBv†–6‚g&WVVæ6–W2Fòf—6—B&Vf÷&RGVæ–ærç’öbF†VÒàÐ¢òòf÷"E42F†W6R6öÖRg&öÒF†R$b6†ææVÂÆâÂ&V6W6R—G0Ð¢òò6†ææVÇ2&Ræ÷BWfVæÇ’76VC²f÷"Ed"F†R†—7F÷&–6Âf—†VB7FW Ð¢òò'’&æGv–GF‚—26÷'&V7BâF†R7F'BæB7F÷g&WVVæ6–W2&÷VæBF†PÐ¢òò66âV—F†W"v’Â6òF†RF–Æör¶VW2v÷&¶–ærVæ6†ævVBàÐ¢&ööÂ$—4E42ÒfÇ6S°Ð¢GVâÓä—4E42†$—4E42“°Ð Ð¢7FC£§fV7F÷#ÅTÄôäsâg&WVVæ6–W3°Ð¢–b†$—4E42’°Ð¢f÷"†–çBä6†ææVÂÒE45ôd•%5Eô4„ääTÃ²ä6†ææVÂÃÒE45ôÄ5EõT„eô4„ääTÃ²ä6†ææVÂ²²’°Ð¢TÄôärVÄ6†ææVÄg&WVVæ7“°Ð¢–b„vWDE446†ææVÄg&WVVæ7’†ä6†ææVÂÂVÄ6†ææVÄg&WVVæ7’Ð¢bbVÄ6†ææVÄg&WVVæ7’ãÒE4BÓäg&WVVæ7•7F'@Ð¢bbVÄ6†ææVÄg&WVVæ7’ÃÒE4BÓäg&WVVæ7•7F÷’°Ð¢g&WVVæ6–W2çW6…ö&6²‡VÄ6†ææVÄg&WVVæ7’“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢f÷"…TÄôärVÄg&WVVæ7’ÒE4BÓäg&WVVæ7•7F'C²VÄg&WVVæ7’ÃÒE4BÓäg&WVVæ7•7F÷²VÄg&WVVæ7’³ÒE4BÓä&æGv–GF‚’°Ð¢g&WVVæ6–W2çW6…ö&6²‡VÄg&WVVæ7’“°Ð¢ÐÐ¢ÐÐ Ð¢f÷"‡6—¦U÷Bä–æFW‚Ò²ä–æFW‚Âg&WVVæ6–W2ç6—¦R‚“²ä–æFW‚²²’°Ð¢6öç7BTÄôärVÄg&WVVæ7’Òg&WVVæ6–W5¶ä–æFW…Ó°Ð¢&ööÂ%7V66VVFVBÒfÇ6S°Ð¢f÷"†–çBäöfg6WE÷2Ò²äöfg6WE÷2Âäöfg6WBbb%7V66VVFVC²äöfg6WE÷2²²’°Ð¢–b…5T44TTDTB‡GVâÓå6WDg&WVVæ7’‡VÄg&WVVæ7’²Äöfg6WG5¶äöfg6WE÷5ÒÂE4BÓä&æGv–GF‚ÂE4BÓå7–Ö&öÅ&FR’’’°Ð¢6ÆVWƒ#“²òòÆWBF†RGVæW"6öÖRF–ÖRFòFWFV7BF†R6–væÀÐ¢–b…5T44TTDTB‡GVâÓävWE7FG2†%&W6VçBÂ$Æö6¶VBÂÄF%7G&VæwF‚ÂÅW&6VçEVÆ—G’’’bb%&W6VçB’°Ð¢£¥6VæDÖW76vR‡E4BÓä‡væBÂtÕõETäU%õ5DE2ÂÄF%7G&VæwF‚ÂÅW&6VçEVÆ—G’“°Ð¢GVâÓå66â‡VÄg&WVVæ7’²Äöfg6WG5¶äöfg6WE÷5ÒÂE4BÓä&æGv–GF‚ÂE4BÓå7–Ö&öÅ&FRÂE4BÓä‡væB“°Ð¢%7V66VVFVBÒG'VS°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢òò7FW2&RVæWfVâVæFW"6†ææVÂÆâÂ6ò&öw&W726÷VçG0Ð¢òòg&WVVæ6–W2f—6—FVB&F†W"F†âF—7Fæ6RG&fVÆÆVBWF†R&æBàÐ¢–çBå&öw&W72Ò×VÄF—b‚†–çB–ä–æFW‚²ÂÂ†–çB–g&WVVæ6–W2ç6—¦R‚’“°Ð¢£¥6VæDÖW76vR‡E4BÓä‡væBÂtÕõETäU%õ44åõ$ôu$U52Âå&öw&W72Â“°Ð¢£¥6VæDÖW76vR‡E4BÓä‡væBÂtÕõETäU%õ5DE2ÂÄF%7G&VæwF‚ÂÅW&6VçEVÆ—G’“°Ð Ð¢–b†Õö%7F÷GVæW%66â’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢£¥6VæDÖW76vR‡E4BÓä‡væBÂtÕõETäU%õ44åôTäBÂÂ“°Ð¢–b‡v57F÷VB’°Ð¢6WD6†ææVÂ„g„vWD6WGF–æw2‚’æäEd$Æ7D6†ææVÂ“°Ð¢ÖVF–6öçG&öÅ7F÷‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð¢òòG–æÖ–2ÖVçW0Ð Ð§fö–B4Ö–äg&ÖS£¤7&VFTG–æÖ–4ÖVçW2‚Ð§°Ð¢dU$”e’†Õö÷Vä4G4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õöf–ÇFW'4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷7V'F—FÆW4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷7V'F—FÆW56V6öæF'”ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†ÕöVF–÷4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷f–FVõ7G&V×4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õö6†FW'4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷F—FÆW4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷Æ–Æ—7DÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õô$EÆ–Æ—7DÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õö6†ææVÇ4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õöff÷&—FW4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷6†FW'4ÖVçRä7&VFU÷WÖVçR‚’“°Ð¢dU$”e’†Õ÷&V6VçDf–ÆW4ÖVçRä7&VFU÷WÖVçR‚’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤FW7G&÷”G–æÖ–4ÖVçW2‚Ð§°Ð¢dU$”e’†Õö÷Vä4G4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õöf–ÇFW'4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷7V'F—FÆW4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷7V'F—FÆW56V6öæF'”ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†ÕöVF–÷4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷f–FVõ7G&V×4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õö6†FW'4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷F—FÆW4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷Æ–Æ—7DÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õô$EÆ–Æ—7DÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õö6†ææVÇ4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õöff÷&—FW4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷6†FW'4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢dU$”e’†Õ÷&V6VçDf–ÆW4ÖVçRäFW7G&÷”ÖVçR‚’“°Ð¢Õöä§V×Fõ7V$ÖVçW46÷VçBÒ°Ð¢&V6VçDf–ÆW4ÖVçTg&öÔÕ%U6WVVæ6RÒÓ°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÆöDG–æÖ–4ÖVçW2‚’°Ð¢òòVç7W&RF†RG–æÖ–6ÆÇ’FFVBÖVçR—FV×2&RWFFV@Ð¢6WGWf–ÇFW'57V$ÖVçR‚“°Ð¢6WGWVF–õ7V$ÖVçR‚“°Ð¢6WGW7V'F—FÆW57V$ÖVçR‚“°Ð¢6WGWf–FVõ7G&V×57V$ÖVçR‚“°Ð¢6WGW§V×Fõ7V$ÖVçW2‚“°Ð¢6WGW&V6VçDf–ÆW57V$ÖVçR‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW÷Vä4E7V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕö÷Vä4G4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôD”ärÇÂg„vWD6WGF–æw2‚’æd†–FT4E$ô×57V$ÖVçR’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”Eôd”ÄUôõTåôõD”4ÅôD•4µõ5D%C°Ð¢f÷"…D4„"G&—fRÒõB‚tr“²G&—fRÃÒõB‚u¢r“²G&—fR²²’°Ð¢4FÄÆ—7CÄ57G&–æsâf–ÆW3°Ð¢÷F–6ÄF—6µG—U÷B÷F–6ÄF—6µG—RÒvWD÷F–6ÄF—6µG—R†G&—fRÂf–ÆW2“°Ð Ð¢–b†÷F–6ÄF—6µG—RÒ÷F–6ÄF—6µôæ÷Df÷VæBbb÷F–6ÄF—6µG—RÒ÷F–6ÄF—6µõVæ¶æ÷vâ’°Ð¢57G&–ærÆ&VÂÒvWDG&—fTÆ&VÂ†G&—fR“°Ð¢–b†Æ&VÂä—4V×G’‚’’°Ð¢7v—F6‚†÷F–6ÄF—6µG—R’°Ð¢66R÷F–6ÄF—6µôVF–ó Ð¢Æ&VÂÒõB‚$VF–ò4B"“°Ð¢'&V³°Ð¢66R÷F–6ÄF—6µõf–FVô4C Ð¢Æ&VÂÒõB‚"…2•d4B"“°Ð¢'&V³°Ð¢66R÷F–6ÄF—6µôEdEf–FVó Ð¢Æ&VÂÒõB‚$EdBf–FVò"“°Ð¢'&V³°Ð¢66R÷F–6ÄF—6µô$C Ð¢Æ&VÂÒõB‚$&ÇR×&’F—62"“°Ð¢'&V³°Ð¢FVfVÇC Ð¢54U%B„dÅ4R“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢57G&–ær7G#°Ð¢7G"äf÷&ÖB…õB‚"W2‚V3¢’"’Â6æ—F—¦TÖVçTÆ&VÂ†Æ&VÂ’ävWE7G&–ær‚’ÂG&—fR“°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â7G"’“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWf–ÇFW'57V$ÖVçR‚Ð§°Ð¢4Õ5F†VÖTÖVçRb7V$ÖVçRÒÕöf–ÇFW'4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢Õ÷'&’å&VÖ÷fTÆÂ‚“°Ð¢Õ÷76'&’å&VÖ÷fTÆÂ‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢T”åB–FbÒ²ò÷W6VB2â–BÂ6òÖ¶Ræöâ×¦W&òFò7F'@Ð¢T”åB–G2Ò”Eôd”ÅDU%5õ5T$•DTÕõ5D%C°Ð¢T”åB–FÂÒ”Eôd”ÅDU%5E$TÕ5õ5T$•DTÕõ5D%C°Ð Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢57G&–ærf–ÇFW$æÖR…6æ—F—¦TÖVçTÆ&VÂ„vWDf–ÇFW$æÖR‡$b’ÂC2’“°Ð Ð¢4Å4”B6Ç6–BÒvWD4Å4”B‡$b“°Ð¢–b†6Ç6–BÓÒ4Å4”Eôd”FV2’°Ð¢46öÕG#Ä•–ãâ–âÒvWDf—'7E–â‡$b“°Ð¢ÕôÔTD”õE•R×C°Ð¢–b‡–âbb5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢Etõ$B2Ò‚…d”DTô”ädô„TDU"¢–×Bç$f÷&ÖB’Óæ&Ö”†VFW"æ&”6ö×&W76–öã°Ð¢7v—F6‚†2’°Ð¢66R$•õ$t# Ð¢f–ÇFW$æÖR³ÒõB‚"…$t"’"“°Ð¢'&V³°Ð¢66R$•õ$ÄSC Ð¢f–ÇFW$æÖR³ÒõB‚"…$ÄSB’"“°Ð¢'&V³°Ð¢66R$•õ$ÄSƒ Ð¢f–ÇFW$æÖR³ÒõB‚"…$ÄS‚’"“°Ð¢'&V³°Ð¢66R$•ô$•Dd”TÄE3 Ð¢f–ÇFW$æÖR³ÒõB‚"„$•Db’"“°Ð¢'&V³°Ð¢FVfVÇC Ð¢f–ÇFW$æÖRäVæDf÷&ÖB…õB‚"‚V2V2V2V2’"’ÀÐ¢…D4„"’‚†2ãâ’b†fb’ÀÐ¢…D4„"’‚†2ãâ‚’b†fb’ÀÐ¢…D4„"’‚†2ãâb’b†fb’ÀÐ¢…D4„"’‚†2ãâ#B’b†fb’“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R–b†6Ç6–BÓÒ4Å4”Eô4Õw&W"’°Ð¢46öÕG#Ä•–ãâ–âÒvWDf—'7E–â‡$b“°Ð¢ÕôÔTD”õE•R×C°Ð¢–b‡–âbb5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢tõ$B2Ò‚…tdTdõ$ÔDU‚¢–×Bç$f÷&ÖB’Óçtf÷&ÖEFs°Ð¢f–ÇFW$æÖRäVæDf÷&ÖB…õB‚"ƒ‚SG‚’"’Â†–çB–2“°Ð¢ÐÐ¢ÒVÇ6R–b†6Ç6–BÓÒõ÷WV–Föb„5FW‡E75F‡'Tf–ÇFW"Ð¢ÇÂ6Ç6–BÓÒõ÷WV–Föb„4çVÆÅFW‡E&VæFW&W"Ð¢ÇÂ6Ç6–BÓÒuT”Dg&öÔ57G&–ær…õB‚'³Cƒ#S#C2Ó$C3’Ó4RÓƒsTBÓc„4#sƒcgÒ"’’’²òò•45 Ð¢òò†–FRF†W6PÐ¢6öçF–çVS°Ð¢ÐÐ Ð¢4ÖVçR–çFW&æÅ7V$ÖVçS°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRä7&VFU÷WÖVçR‚’“°Ð Ð¢–çBåvW2Ò°Ð Ð¢46öÕ•G#Ä•7V6–g•&÷W'G•vW3â5Ò$c°Ð Ð¢Õ÷'&’äFB‡$b“°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–G2Â&W57G"„”E5ôÔ”äe$Õób’’“°Ð Ð¢åvW2²³°Ð Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢57G&–ær–äæÖRÒ6æ—F—¦TÖVçTÆ&VÂ„vWE–äæÖR‡–â’“°Ð Ð¢–b‡5Ò–â’°Ð¢4UT”B6uT”C°Ð¢6uT”BçVÆV×2ÒçVÆÇG#°Ð¢–b…5T44TTDTB‡5ÓävWEvW2‚f6uT”B’’bb6uT”Bæ4VÆV×2â’°Ð¢Õ÷'&’äFB‡–â“°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–G2²åvW2Â–äæÖR²&W57G"„”E5ôÔ”äe$Õór’’“°Ð Ð¢–b†6uT”BçVÆV×2’°Ð¢6õF6´ÖVÔg&VR†6uT”BçVÆV×2“°Ð¢ÐÐ Ð¢åvW2²³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð Ð¢46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ52Ò$c°Ð¢Etõ$Bå7G&V×2Ò°Ð¢–b‡52bb5T44TTDTB‡52Óä6÷VçB‚få7G&V×2’’’°Ð¢Etõ$BfÆw2ÒEtõ$EôÔƒ°Ð¢Etõ$Bw&÷WÒEtõ$EôÔƒ°Ð¢Etõ$B&Wfw&÷WÒEtõ$EôÔƒ°Ð¢Ä4”BÆ6–BÒ°Ð¢t4„"¢væÖRÒçVÆÇG#°Ð¢T”åBTÖVçTfÆw3°Ð Ð¢–b†å7G&V×2âbbåvW2â’°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"ÂÔeôTä$ÄTB’“°Ð¢ÐÐ Ð¢T”åB–FÇ7F'BÒ–FÃ°Ð¢T”åB6VÆV7FVD–äw&÷WÒ°Ð Ð¢f÷"„Etõ$B’Ò²’Âå7G&V×3²’²²’°Ð¢Õ÷76'&’äFB‡52“°Ð Ð¢fÆw2Òw&÷WÒ°Ð¢væÖRÒçVÆÇG#°Ð¢–b„d”ÄTB‡52Óä–æfò†’ÂçVÆÇG"ÂffÆw2ÂfÆ6–BÂfw&÷WÂgvæÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†w&÷WÒ&Wfw&÷Wbb–FÂâ–FÇ7F'B’°Ð¢–b‡6VÆV7FVD–äw&÷W’°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒ†–FÇ7F'BÂ–FÂÒÂ6VÆV7FVD–äw&÷WÂÔeô%”4ôÔÔäB’“°Ð¢6VÆV7FVD–äw&÷WÒ°Ð¢ÐÐ¢dU$”e’†–çFW&æÅ7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"ÂÔeôTä$ÄTB’“°Ð¢–FÇ7F'BÒ–FÃ°Ð¢ÐÐ¢&Wfw&÷WÒw&÷W°Ð Ð¢TÖVçTfÆw2ÒÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†fÆw2bÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’°Ð¢6VÆV7FVD–äw&÷WÒ–FÃ°Ð¢ÒVÇ6R–b†fÆw2bÕ5E$TÕ4TÄT5D”ädõôTä$ÄTB’°Ð¢TÖVçTfÆw2ÃÒÔeô4„T4´TC°Ð¢ÐÐ Ð¢57G&–ær7G&VÔæÖS°Ð¢–b‚væÖR’°Ð¢7G&VÔæÖRäÆöE7G&–ær„”E5ôuõTä´äõtåõ5E$TÒ“°Ð¢7G&VÔæÖRäVæDf÷&ÖB…õB‚"VÇR"’Â’²“°Ð¢ÒVÇ6R°Ð¢7G&VÔæÖRÒ6æ—F—¦TÖVçTÆ&VÂ‡væÖR“°Ð¢6õF6´ÖVÔg&VR‡væÖR“°Ð¢ÐÐ Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRäVæDÖVçR‡TÖVçTfÆw2Â–FÂ²²Â7G&VÔæÖR’“°Ð¢ÐÐ¢–b‡6VÆV7FVD–äw&÷W’°Ð¢dU$”e’†–çFW&æÅ7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒ†–FÇ7F'BÂ–FÂÒÂ6VÆV7FVD–äw&÷WÂÔeô%”4ôÔÔäB’“°Ð¢ÐÐ Ð¢–b†å7G&V×2ÓÒ’°Ð¢52å&VÆV6R‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b†åvW2ÓÒbb52’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–G2Âf–ÇFW$æÖR’“°Ð¢ÒVÇ6R°Ð¢–b†åvW2âÇÂ52’°Ð¢T”åBäfÆw2ÒÔeõ5E$”ärÂÔeõõUÂ‚‡5ÇÂ52’òÔeôTä$ÄTB¢Ôeôu$”TB“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†äfÆw2Â…T”åEõE"––çFW&æÅ7V$ÖVçRäFWF6‚‚’Âf–ÇFW$æÖR’“°Ð¢ÒVÇ6R°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôu$”TBÂ–FbÂf–ÇFW$æÖR’“°Ð¢ÐÐ¢ÐÐ Ð¢–G2³ÒåvW3°Ð¢–Fb²³°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð Ð¢–b‡7V$ÖVçRävWDÖVçT—FVÔ6÷VçB‚’â’°Ð¢dU$”e’‡7V$ÖVçRä–ç6W'DÖVçRƒÂÔeõ5E$”ärÂÔeôTä$ÄTBÂÔeô%•õ4•D”ôâÂ”Eôd”ÅDU%5ô4õ•õDõô4Ä•$ô$BÂ&W57G"„”E5ôd”ÅDU%5ô4õ•õDõô4Ä•$ô$B’’“°Ð¢dU$”e’‡7V$ÖVçRä–ç6W'DÖVçRƒÂÔeõ4U$Dõ"ÂÔeôTä$ÄTBÂÔeô%•õ4•D”ôâ’“°Ð¢ÐÐ¢7V$ÖVçRægVÆf–ÆÅF†VÖU&W2‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWVF–õ7V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕöVF–÷4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”EôTD”õõ5T$•DTÕõ5D%C°Ð Ð¢Etõ$B57G&V×2Ò°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢7W'&VçDVF–ôÆærÒõB‚""“°Ð¢TÄôärVÅ7G&V×4f–Æ&ÆRÂVÄ7W'&VçE7G&VÓ°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWD7W'&VçDVF–ò‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒ’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢Ä4”BFVdÆæwVvS°Ð¢EdEôTD”õôÄäuôU…BW‡C°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWDFVfVÇDVF–ôÆæwVvR‚dFVdÆæwVvRÂfW‡B’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢f÷"…TÄôär’Ò²’ÂVÅ7G&V×4f–Æ&ÆS²’²²’°Ð¢Ä4”BÆæwVvS°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWDVF–ôÆæwVvR†’ÂdÆæwVvR’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b„ÆæwVvRÓÒFVdÆæwVvR’°Ð¢fÆw2ÃÒÔeôDTdTÅC°Ð¢ÐÐ¢–b†’ÓÒVÄ7W'&VçE7G&VÒ’°Ð¢fÆw2ÃÒÔeô4„T4´TC°Ð¢–b„ÆæwVvR’°Ð¢vWDÆö6ÆU7G&–ær„ÆæwVvRÂÄô4ÄUõ4•4óc3”ÄätäÔS"Â7W'&VçDVF–ôÆær“°Ð¢ÐÐ¢ÐÐ Ð¢57G&–ær7G#°Ð¢–b„ÆæwVvR’°Ð¢vWDÆö6ÆU7G&–ær„ÆæwVvRÂÄô4ÄUõ4TätÄäuTtRÂ7G"“°Ð¢ÒVÇ6R°Ð¢7G"äf÷&ÖB„”E5ôuõTä´äõtâÂ’²“°Ð¢ÐÐ Ð¢EdEôVF–ôGG&–'WFW2E#°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWDVF–ôGG&–'WFW2†’ÂdE"’’’°Ð¢7v—F6‚„E"äÆæwVvTW‡FVç6–öâ’°Ð¢66REdEôTEôU…Eôæ÷E7V6–f–VC Ð¢FVfVÇC Ð¢'&V³°Ð¢66REdEôTEôU…Eô6F–öç3 Ð¢7G"³ÒõB‚"„6F–öç2’"“°Ð¢'&V³°Ð¢66REdEôTEôU…Eõf—7VÆÇ”–×—&VC Ð¢7G"³ÒõB‚"…f—7VÆÇ’–×—&VB’"“°Ð¢'&V³°Ð¢66REdEôTEôU…EôF—&V7F÷$6öÖÖVçG3 Ð¢7G"äVæDf÷&ÖB„”E5ôÔ”äe$Õó#“°Ð¢'&V³°Ð¢66REdEôTEôU…EôF—&V7F÷$6öÖÖVçG3# Ð¢7G"äVæDf÷&ÖB„”E5ôÔ”äe$Õó#"“°Ð¢'&V³°Ð¢ÐÐ Ð¢57G&–ærf÷&ÖBÒvWDEdDVF–ôf÷&ÖDæÖR„E"“°Ð Ð¢–b‚f÷&ÖBä—4V×G’‚’’°Ð¢7G"äf÷&ÖB„”E5ôÔ”äe$ÕóÀÐ¢57G&–ær‡7G"’ävWE7G&–ær‚’ÀÐ¢f÷&ÖBävWE7G&–ær‚’ÀÐ¢E"æGtg&WVVæ7’ÀÐ¢E"æ%VçF—¦F–öâÀÐ¢E"æ$çVÖ&W$öd6†ææVÇ2ÀÐ¢&W57G"„E"æ$çVÖ&W$öd6†ææVÇ2âò”E5ôÔ”äe$Õó2¢”E5ôÔ”äe$Õó"’ävWE7G&–ær‚Ð¢“°Ð¢ÐÐ¢ÐÐ Ð¢dU$”e’„VæDÖVçTW‚‡7V$ÖVçRÂfÆw2Â–B²²Â7G"’“°Ð¢ÐÐ¢ÐÐ¢òò–bf–Æ&ÆRW6RF†RVF–ò7v—F6†W"f÷"WfW'—F†–ær'WBEdG0Ð¢VÇ6R–b†Õ÷VF–õ7v—F6†W%52bb5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä6÷VçB‚f57G&V×2’’bb57G&V×2â’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%D•DÄU5ôõD”ôå2’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"ÂÔeôTä$ÄTB’“°Ð Ð¢Æöær•6VÂÒ°Ð Ð¢f÷"†Æöær’Ò²’Â†Æöær–57G&V×3²’²²’°Ð¢Etõ$BGtfÆw3°Ð¢t4„"¢æÖRÒçVÆÇG#°Ð¢–b„d”ÄTB†Õ÷VF–õ7v—F6†W%52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂçVÆÇG"ÂgæÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢'&V³°Ð¢ÐÐ¢–b†GtfÆw2’°Ð¢•6VÂÒ“°Ð¢ÐÐ Ð¢57G&–æræÖR…6æ—F—¦TÖVçTÆ&VÂ‡æÖR’“°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²ÂæÖR’“°Ð Ð¢6õF6´ÖVÔg&VR‡æÖR“°Ð¢ÐÐ¢dU$”e’‡7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒƒ"Â"²57G&V×2ÒÂ"²•6VÂÂÔeô%•õ4•D”ôâ’“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRÇÂvWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢6WGWæe7G&VÕ6VÆV7E7V$ÖVçR‡7V$ÖVçRÂ–BÂ“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW7V'F—FÆW57V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕ÷7V'F—FÆW4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTBÇÂÕödVF–ôöæÇ’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”Eõ5T%D•DÄU5õ5T$•DTÕõ5D%C°Ð Ð¢òòEdB7V'F—FÆW2–âEdBÖöFR&RæWfW"†æFÆVB'’F†R–çFW&æÂ7V'F—FÆW2&VæFW&W Ð¢òò'WB—B—27F–ÆÂ÷76–&ÆRFòÆöBW‡FW&æÂ7V'F—FÆW26òvR¶VWF†B–b&Æö6°Ð¢òò6W&FVBg&öÒF†R&W7@Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢TÄôärVÅ7G&V×4f–Æ&ÆRÂVÄ7W'&VçE7G&VÓ°Ð¢$ôôÂ$—4F—6&ÆVC°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçE7V'–7GW&R‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒÂf$—4F—6&ÆVB’Ð¢bbVÅ7G&V×4f–Æ&ÆRâ’°Ð¢Ä4”BFVdÆæwVvS°Ð¢EdEõ5T%”5EU$UôÄäuôU…BW‡C°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWDFVfVÇE7V'–7GW&TÆæwVvR‚dFVdÆæwVvRÂfW‡B’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂ†$—4F—6&ÆVBò¢Ôeô4„T4´TB’Â–B²²Â&W57G"„”E5ôEdEõ5T%D•DÄU5ôTä$ÄR’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"ÂÔeôTä$ÄTB’“°Ð Ð¢f÷"…TÄôär’Ò²’ÂVÅ7G&V×4f–Æ&ÆS²’²²’°Ð¢Ä4”BÆæwVvS°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWE7V'–7GW&TÆæwVvR†’ÂdÆæwVvR’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b„ÆæwVvRÓÒFVdÆæwVvR’°Ð¢fÆw2ÃÒÔeôDTdTÅC°Ð¢ÐÐ¢–b†’ÓÒVÄ7W'&VçE7G&VÒ’°Ð¢fÆw2ÃÒÔeô4„T4´TC°Ð¢ÐÐ Ð¢57G&–ær7G#°Ð¢–b„ÆæwVvR’°Ð¢vWDÆö6ÆU7G&–ær„ÆæwVvRÂÄô4ÄUõ4TätÄäuTtRÂ7G"“°Ð¢ÒVÇ6R°Ð¢7G"äf÷&ÖB„”E5ôuõTä´äõtâÂ’²“°Ð¢ÐÐ Ð¢EdEõ7V'–7GW&TGG&–'WFW2E#°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWE7V'–7GW&TGG&–'WFW2†’ÂdE"’’’°Ð¢7v—F6‚„E"äÆæwVvTW‡FVç6–öâ’°Ð¢66REdEõ5ôU…Eôæ÷E7V6–f–VC Ð¢FVfVÇC Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåôæ÷&ÖÃ Ð¢7G"³ÒõB‚""“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåô&–s Ð¢7G"³ÒõB‚"„&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„6†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ôæ÷&ÖÃ Ð¢7G"³ÒõB‚"„42’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ô&–s Ð¢7G"³ÒõB‚"„42&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„426†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eôf÷&6VC Ð¢7G"³ÒõB‚"„f÷&6VB’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ôæ÷&ÖÃ Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ô&–s Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2Â&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2Â6†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢dU$”e’„VæDÖVçTW‚‡7V$ÖVçRÂfÆw2Â–B²²Â7G"’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢Etõ$B6VÆV7FVBÒ6WGWæe7G&VÕ6VÆV7E7V$ÖVçR‡7V$ÖVçRÂ–BÂ"“°Ð¢–b‡6VÆV7FVBÒÓ’°Ð¢6WE7V'F—FÆR‡6VÆV7FVBÒ”Eõ5T%D•DÄU5õ5T$•DTÕõ5D%B“°Ð¢ÐÐ¢ÒVÇ6R–b‡÷2’²òò–çFW&æÂ7V'F—FÆW2&VæFW&W Ð¢–çBä—FV×4&Vf÷&U7F'BÒ–BÒ”Eõ5T%D•DÄU5õ5T$•DTÕõ5D%C°Ð¢–b†ä—FV×4&Vf÷&U7F'Bâ’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢ä—FV×4&Vf÷&U7F'B³Ò#²òò6W&F÷'0Ð¢ÐÐ Ð¢òò'V–ÆBF†R7FF–2ÖVçRw2—FV×0Ð¢&ööÂ%FW‡E7V'F—FÆW2ÒfÇ6S°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%D•DÄU5ôõD”ôå2’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%D•DÄU5õ5E”ÄU2’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%D•DÄU5õ$TÄôB’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%D•DÄU5ô„”DR’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%ôõdU%$”DUôDTdTÅEõ5E”ÄR’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5õ5T%ôõdU%$”DUôÄÅõ5E”ÄU2’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð Ð¢òò'V–ÆBF†RG–æÖ–2ÖVçRw2—FV×0Ð¢–çB’ÒÂ•6VÆV7FVBÒÓ°Ð¢v†–ÆR‡÷2’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBç6÷W&6Tf–ÇFW"’°Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB‡54bÓä6÷VçB‚f57G&V×2’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢f÷"†–çB¢ÒÂ6çBÒ†–çB–57G&V×3²¢Â6çC²¢²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð¢Ä4”BÆ6–BÒ°Ð¢–b„d”ÄTB‡54bÓä–æfò†¢ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’Ð¢ÇÂ7¤æÖR’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†Gtw&÷WÒ"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÐÐ¢bbGtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢•6VÆV7FVBÒ“°Ð¢ÐÐ Ð¢òöF"–âæÖR6öÖ–ærg&öÒF†R7Æ—GFW"—2'BöbF†RæÖRÂæ÷B6öÇVÖàÐ¢57G&–æræÖRÒ6æ—F—¦TÖVçTÆ&VÂ„57G&–ær‡7¤æÖR’“°Ð¢ò Ð¢57G&–ærÆ6æÖRÒ57G&–ær†æÖR’äÖ¶TÆ÷vW"‚“°Ð¢–b†Æ6æÖRäf–æB…õB‚"öfb"’’ãÒ’°Ð¢æÖRäÆöE7G&–ær„”E5ôuôD•4$ÄTB“°Ð¢ÐÐ¢¢ðÐ¢–b†Æ6–BÒ’°Ð¢57G&–ærÆ6–G7G#°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4TätÄäuTtRÂÆ6–G7G"“°Ð¢æÖRäVæB…õB‚%ÇB"’²Æ6–G7G"“°Ð¢ÐÐ Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²ÂæÖR’“°Ð¢’²³°Ð¢ÐÐ¢ÒVÇ6R°Ð¢46öÕG#Ä•7V%7G&VÓâ7V%7G&VÒÒ7V$–çWBç7V%7G&VÓ°Ð¢–b‚7V%7G&VÒ’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢•6VÆV7FVBÒ’²7V%7G&VÒÓävWE7G&VÒ‚“°Ð¢ÐÐ Ð¢f÷"†–çB¢ÒÂ6çBÒ7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“²¢Â6çC²¢²²’°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢Ä4”BÆ6–BÒ°Ð¢–b…5T44TTDTB‡7V%7G&VÒÓävWE7G&VÔ–æfò†¢ÂgæÖRÂfÆ6–B’’’°Ð¢57G&–æræÖR‡æÖR“°Ð¢–b†Æ6–BÒbbæÖRäf–æB„ÂuÇBr’Â’°Ð¢57G&–ærÆ6–G7G#°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4TätÄäuTtRÂÆ6–G7G"“°Ð¢æÖRäVæB…õB‚%ÇB"’²Æ6–G7G"“°Ð¢ÐÐ Ð¢æÖRÒ6æ—F—¦TÖVçTÆ&VÂ†æÖRÂÔTåUôäÔUôÔ‚ÂG'VR“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²ÂæÖR’“°Ð¢ÒVÇ6R°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5ôuõTä´äõtåõ5E$TÒ’’“°Ð¢ÐÐ¢’²³°Ð¢ÐÐ¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢4Å4”B6Ç6–C°Ð¢–b…5T44TTDTB‡7V$–çWBç7V%7G&VÒÓävWD6Æ74”B‚f6Ç6–B’Ð¢bb6Ç6–BÓÒõ÷WV–Föb„5&VæFW&VEFW‡E7V'F—FÆR’’°Ð¢%FW‡E7V'F—FÆW2ÒG'VS°Ð¢ÐÐ¢ÐÐ Ð¢òòDôDó¢f–æB&WGFW"v’Fòw&÷WF†W6RVçG&–W0Ð¢ò¦–b‡÷2bbÕ÷7V%7G&V×2ävWDB‡÷2’ç7V%7G&VÒ’°Ð¢4Å4”B7W"ÂæW‡C°Ð¢7V%7G&VÒÓävWD6Æ74”B‚f7W"“°Ð¢Õ÷7V%7G&V×2ävWDB‡÷2’ç7V%7G&VÒÓävWD6Æ74”B‚fæW‡B“°Ð Ð¢–b†7W"ÒæW‡B’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢ÐÐ¢Ò¢ðÐ¢ÐÐ Ð¢òò6WBF†RÖVçRw2—FV×2r7FFPÐ¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢òò7G–ÆPÐ¢–b‚%FW‡E7V'F—FÆW2’°Ð¢7V$ÖVçRäVæ&ÆTÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²ÂÔeô%•õ4•D”ôâÂÔeôu$”TB“°Ð¢ÐÐ¢òò†–FPÐ¢–b‚2ædVæ&ÆU7V'F—FÆW2’°Ð¢7V$ÖVçRä6†V6´ÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²BÂÔeô%•õ4•D”ôâÂÔeô4„T4´TB“°Ð¢ÐÐ¢òò7G–ÆR÷fW'&–FW0Ð¢–b‚%FW‡E7V'F—FÆW2’°Ð¢7V$ÖVçRäVæ&ÆTÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²RÂÔeô%•õ4•D”ôâÂÔeôu$”TB“°Ð¢7V$ÖVçRäVæ&ÆTÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²bÂÔeô%•õ4•D”ôâÂÔeôu$”TB“°Ð¢ÐÐ¢–b‡2æ%7V'F—FÆT÷fW'&–FTFVfVÇE7G–ÆR’°Ð¢7V$ÖVçRä6†V6´ÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²RÂÔeô%•õ4•D”ôâÂÔeô4„T4´TB“°Ð¢ÐÐ¢–b‡2æ%7V'F—FÆT÷fW'&–FTÆÅ7G–ÆW2’°Ð¢7V$ÖVçRä6†V6´ÖVçT—FVÒ†ä—FV×4&Vf÷&U7F'B²bÂÔeô%•õ4•D”ôâÂÔeô4„T4´TB“°Ð¢ÐÐ¢–b†•6VÆV7FVBãÒ’°Ð¢dU$”e’‡7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒ†ä—FV×4&Vf÷&U7F'B²‚Âä—FV×4&Vf÷&U7F'B²‚²’ÒÂä—FV×4&Vf÷&U7F'B²‚²•6VÆV7FVBÂÔeô%•õ4•D”ôâ’“°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢6WGWæe7G&VÕ6VÆV7E7V$ÖVçR‡7V$ÖVçRÂ–BÂ"“°Ð¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4VÆ–v–&ÆU6V6öæF'•7V'F—FÆR†6öç7B7V'F—FÆT–çWBb7V$–çWB’6öç7@Ð§°Ð¢òòöæÇ’W‡FW&æÆÇ’ÆöFVBFW‡B7V'F—FÆW26â&RW6VB2F†R6V6öæF'’G&6²ÀÐ¢òòæBæWfW"F†R7G&VÒF†B—27W'&VçFÇ’6VÆV7FVB2F†R&–Ö'’öæRàÐ¢òòVÖ&VFFVBô”Õ7G&VÕ6VÆV7BG&6·2&RW†6ÇVFVB&V6W6R6VÆV7F–æröæR6ÆÇ0Ð¢òò”Õ7G&VÕ6VÆV7C£¤Væ&ÆRÂv†–6‚v÷VÆBF—7GW&"F†R&–Ö'’6VÆV7F–öâàÐ¢–b‚7V$–çWBç7V%7G&VÒÇÂ7V$–çWBç6÷W&6Tf–ÇFW Ð¢ÇÂ7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÐÐ¢ÇÂ7FC£¦f–æB†ÕôW‡FW&æÅ7V'7G&V×2æ6&Vv–â‚’ÂÕôW‡FW&æÅ7V'7G&V×2æ6VæB‚’ÀÐ¢„•7V%7G&VÒ¢—7V$–çWBç7V%7G&VÒ’ÓÒÕôW‡FW&æÅ7V'7G&V×2æ6VæB‚’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢WFò%E2ÒG–æÖ–5ö67CÄ5&VæFW&VEFW‡E7V'F—FÆR£â‚„•7V%7G&VÒ¢—7V$–çWBç7V%7G&VÒ“°Ð¢–b‚%E2’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢òò&W7G&–7BFò6–×ÆRFW‡Bf÷&ÖG3¢54ô52æBF†R„ÔÂÖ&6VBf÷&ÖG26àÐ¢òò6''’F†V—"÷vâ÷6—F–öæ–ærÂv†–6‚v÷VÆB6öÆÆ–FRv—F‚F†R&–Ö'’G&6²àÐ¢7v—F6‚‡%E2ÓæÕ÷7V'F—FÆUG—R’°Ð¢66R7V'F—FÆS£¥5%C Ð¢66R7V'F—FÆS£¥5T# Ð¢66R7V'F—FÆS£¥4Ô“ Ð¢66R7V'F—FÆS£¥4# Ð¢66R7V'F—FÆS£¥E…C Ð¢66R7V'F—FÆS£¥%C Ð¢66R7V'F—FÆS£¥eEC Ð¢&WGW&âG'VS°Ð¢FVfVÇC Ð¢&WGW&âfÇ6S°Ð¢ÐÐ§ÐÐ Ð¥7V'F—FÆT–çWB¢4Ö–äg&ÖS£¤vWE6V6öæF'•7V'F—FÆT–çWB†–çB–G‚Ð§°Ð¢òò&WGW&ç2F†R–G‚×F‚ƒÖ&6VB’VÆ–v–&ÆR6V6öæF'’7V'F—FÆR7G&VÒÂ÷"çVÆÇG"àÐ¢–b†–G‚ãÒ’°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð¢–b„—4VÆ–v–&ÆU6V6öæF'•7V'F—FÆR‡7V$–çWB’bb–G‚ÒÒÓÒ’°Ð¢&WGW&âg7V$–çWC°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢&WGW&âçVÆÇG#°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW6V6öæF'•7V'F—FÆU7V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕ÷7V'F—FÆW56V6öæF'”ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTBÇÂÕödVF–ôöæÇ’ÇÂÕ÷4’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”Eõ5T%D•DÄU5õ4T4ôäD%•õ5T$•DTÕõ5D%C°Ð¢–çB’ÒÂ•6VÆV7FVBÒÓ°Ð Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð¢–b‚—4VÆ–v–&ÆU6V6öæF'•7V'F—FÆR‡7V$–çWB’’°Ð¢6öçF–çVS°Ð¢ÐÐ¢–b†’ÓÒ’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²Â&W57G"„”E5ôuôD•4$ÄTB’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢ÐÐ¢òòæWfW"†æB÷WB6öÖÖæB–B&W–öæBF†RF—7F6†VB&ævPÐ¢–b†–Bâ”Eõ5T%D•DÄU5õ4T4ôäD%•õ5T$•DTÕôTäB’°Ð¢'&V³°Ð¢ÐÐ¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷6V6öæF'•7V$–çWBç7V%7G&VÒ’°Ð¢•6VÆV7FVBÒ“°Ð¢ÐÐ Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢57G&–æræÖS°Ð¢–b…5T44TTDTB‡7V$–çWBç7V%7G&VÒÓävWE7G&VÔ–æfòƒÂgæÖRÂçVÆÇG"’’bbæÖR’°Ð¢æÖRÒ6æ—F—¦TÖVçTÆ&VÂ„57G&–ær‡æÖR’ÂÔTåUôäÔUôÔ‚ÂG'VR“°Ð¢ÒVÇ6R°Ð¢æÖRäÆöE7G&–ær„”E5ôuõTä´äõtåõ5E$TÒ“°Ð¢ÐÐ¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ–B²²ÂæÖR’“²òòVçG'’’—2BÖVçR÷6—F–öâ’² Ð¢’²³°Ð¢ÐÐ Ð¢–b†’â’°Ð¢òò6†V6²F†R7F—fRVçG'’Â÷"$F—6&ÆVB"‡÷6—F–öâ’v†Vâæò6V6öæF'’—26VÆV7FV@Ð¢–çB6†V6µ÷2Ò†•6VÆV7FVBãÒ’ò†•6VÆV7FVB²"’¢°Ð¢dU$”e’‡7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒƒÂ7V$ÖVçRävWDÖVçT—FVÔ6÷VçB‚’ÒÂ6†V6µ÷2ÂÔeô%•õ4•D”ôâ’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢ÐÐ Ð¢òòÆöB7V'F—FÆRf–ÆRF—&V7FÇ’2F†R6V6öæF'’G&6²Âv—F†÷WBvö–æpÐ¢òòF‡&÷Vv‚F†R&VwVÆ"ÆöBF‚v†–6‚6†ævW2F†R&–Ö'’6VÆV7F–öâàÐ¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõ5T%D•DÄU5õ4T4ôäD%•ôÄôBÂ&W57G"„”E5ôuôÄôEõ5T%D•DÄU2’’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWf–FVõ7G&V×57V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕ÷f–FVõ7G&V×4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”Eõd”DTõõ5E$TÕ5õ5T$•DTÕõ5D%C°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢6WGWæe7G&VÕ6VÆV7E7V$ÖVçR‡7V$ÖVçRÂ–BÂ“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢TÄôärVÅ7G&V×4f–Æ&ÆRÂVÄ7W'&VçE7G&VÓ°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWD7W'&VçDævÆR‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒ’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b‡VÅ7G&V×4f–Æ&ÆRÂ"’°Ð¢&WGW&ã²òòöæR6†ö–6R—2æ÷B6†ö–6RââàÐ¢ÐÐ Ð¢f÷"…TÄôär’Ò²’ÃÒVÅ7G&V×4f–Æ&ÆS²’²²’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†’ÓÒVÄ7W'&VçE7G&VÒ’°Ð¢fÆw2ÃÒÔeô4„T4´TC°Ð¢ÐÐ Ð¢57G&–ær7G#°Ð¢7G"äf÷&ÖB„”E5ôuôätÄRÂ’“°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–B²²Â7G"’“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW§V×Fõ7V$ÖVçW2„4ÖVçR¢&VçDÖVçRò£ÒçVÆÇG"¢òÂ–çB”–ç6W'E÷2ò£ÒÓ¢òÐ§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢WFòV×G”ÖVçRÒ²eÒ„4Õ5F†VÖTÖVçRbÖVçR’°Ð¢v†–ÆR†ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð¢Ó°Ð Ð¢òòV×G’F†R7V&ÖVçW0Ð¢V×G”ÖVçR†Õö6†FW'4ÖVçR“°Ð¢V×G”ÖVçR†Õ÷F—FÆW4ÖVçR“°Ð¢V×G”ÖVçR†Õ÷Æ–Æ—7DÖVçR“°Ð¢V×G”ÖVçR†Õô$EÆ–Æ—7DÖVçR“°Ð¢V×G”ÖVçR†Õö6†ææVÇ4ÖVçR“°Ð¢òò&VÖ÷fRF†R7V&ÖVçW2g&öÒF†R$æf–vFR"ÖVçPÐ¢–b‡&VçDÖVçRbb”–ç6W'E÷2ãÒ’°Ð¢f÷"ƒ²Õöä§V×Fõ7V$ÖVçW46÷VçBâ²Õöä§V×Fõ7V$ÖVçW46÷VçBÒÒ’°Ð¢dU$”e’‡&VçDÖVçRÓå&VÖ÷fTÖVçR†”–ç6W'E÷2ÂÔeô%•õ4•D”ôâ’“°Ð¢ÐÐ¢ÐÐ Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢T”åB–BÒ”Eôäd”tDUô¥TÕDõõ5T$•DTÕõ5D%BÂ–E7F'BÂ–E6VÆV7FVC°Ð Ð¢WFòÖVçU7F'E&F–õ6V7F–öâÒ²eÒ‚’°Ð¢–E7F'BÒ–C°Ð¢–E6VÆV7FVBÒT”åEôU%$õ#°Ð¢Ó°Ð¢WFòÖVçTVæE&F–õ6V7F–öâÒ²eÒ„4ÖVçRbÖVçR’°Ð¢–b†–E6VÆV7FVBÒT”åEôU%$õ"’°Ð¢dU$”e’†ÖVçRä6†V6´ÖVçU&F–ô—FVÒ†–E7F'BÂ–BÒÂ–E6VÆV7FVBÀÐ¢–E7F'BãÒ”Eôäd”tDUô¥TÕDõõ5T$•DTÕõ5D%BòÔeô%”4ôÔÔäB¢Ôeô%•õ4•D”ôâ’“°Ð¢ÐÐ¢Ó°Ð¢WFòFE7V$ÖVçT–e÷76–&ÆRÒ²eÒ„57G&–ær7V$ÖVçTæÖRÂ4ÖVçRb7V$ÖVçR’°Ð¢–b‡&VçDÖVçRbb”–ç6W'E÷2ãÒ’°Ð¢–b‡&VçDÖVçRÓä–ç6W'DÖVçR†”–ç6W'E÷2²Õöä§V×Fõ7V$ÖVçW46÷VçBÂÔeõõUÂÔeô%•õ4•D”ôâÀÐ¢…T”åEõE"’„„ÔTåR—7V$ÖVçRÂ7V$ÖVçTæÖR’’°Ð¢4Õ5F†VÖTÖVçS£¦gVÆf–ÆÅF†VÖU&W4—FVÒ‡&VçDÖVçRÂ”–ç6W'E÷2²Õöä§V×Fõ7V$ÖVçW46÷VçB“°Ð¢Õöä§V×Fõ7V$ÖVçW46÷VçB²³°Ð¢ÒVÇ6R°Ð¢54U%B„dÅ4R“°Ð¢ÐÐ¢ÐÐ¢Ó°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢–b†ÕôÕÅ5Æ–Æ—7Bç6—¦R‚’â’°Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢57G&–ærÅöÆ&VÂÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWD†VB‚’ävWDÆ&VÂ‚“°Ð¢f÷"†WFòb—FVÒ¢ÕôÕÅ5Æ–Æ—7B’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢57G&–ærF–ÖRÒõB‚%²"’²&VgF–ÖUFõ7G&–æs"„—FVÒäGW&F–öâ‚’’²õB‚%Ò"“°Ð¢57G&–æræÖRÒF…WF–Ç3£¥7G&—F„÷%W&Â„—FVÒæÕ÷7G$f–ÆTæÖR“°Ð Ð¢–b‚ÅöÆ&VÂä—4V×G’‚’bbæÖRÓÒÅöÆ&VÂ’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ Ð¢æÖRÒ6æ—F—¦TÖVçTÆ&VÂ†æÖR“°Ð¢dU$”e’†Õô$EÆ–Æ—7DÖVçRäVæDÖVçR†fÆw2Â–B²²ÂæÖR²uÇBr²F–ÖR’“°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õô$EÆ–Æ—7DÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUô$EõÄ”Ä•5E2’ÂÕô$EÆ–Æ—7DÖVçR“°Ð¢ÐÐ Ð¢òõ6WGW6†FW'2‚“°Ð¢–b†Õ÷4"bbÕ÷4"Óä6†vWD6÷VçB‚’â’°Ð¢$TdU$Tä4UõD”ÔR'BÒvWE÷2‚“°Ð¢Etõ$B¢ÒÕ÷4"Óä6†Æöö·W‚g'BÂçVÆÇG"“°Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢f÷"„Etõ$B’Ò²’ÂÕ÷4"Óä6†vWD6÷VçB‚“²’²²Â–B²²’°Ð¢'BÒ°Ð¢46öÔ%5E"'7G#°Ð¢–b„d”ÄTB†Õ÷4"Óä6†vWB†’Âg'BÂf'7G"’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢57G&–ærF–ÖRÒõB‚%²"’²&VgF–ÖUFõ7G&–æs"‡'B’²õB‚%Ò"“°Ð Ð¢57G&–æræÖRÒ6æ—F—¦TÖVçTÆ&VÂ„57G&–ær†'7G"’“°Ð Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†’ÓÒ¢’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ Ð¢dU$”e’†Õö6†FW'4ÖVçRäVæDÖVçR†fÆw2Â–BÂæÖR²uÇBr²F–ÖR’“°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õö6†FW'4ÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUô4„DU%2’ÂÕö6†FW'4ÖVçR“°Ð¢ÐÐ Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’â’°Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢õ4•D”ôâ÷2ÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2bb–BÂ”Eôäd”tDUô¥TÕDõõ5T$•DTÕõ5D%B²#‚’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b‡÷2ÓÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWE÷2‚’’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ¢5Æ–Æ—7D—FVÒbÆ’ÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWDæW‡B‡÷2“°Ð¢57G&–æræÖRÒ6æ—F—¦TÖVçTÆ&VÂ‡Æ’ävWDÆ&VÂ‚’“°Ð¢dU$”e’†Õ÷Æ–Æ—7DÖVçRäVæDÖVçR†fÆw2Â–B²²ÂæÖR’“°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õ÷Æ–Æ—7DÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUõÄ”Ä•5B’ÂÕ÷Æ–Æ—7DÖVçR“°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢TÄôärVÄçVÔöeföÇVÖW2ÂVÅföÇVÖRÂVÄçVÔöeF—FÆW2ÂVÄçVÔöd6†FW'2ÂVÅTõ3°Ð¢EdEôD•45õ4”DR6–FS°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö6F–öã°Ð Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚dÆö6F–öâ’Ð¢bb5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçETõ2‚gVÅTõ2’Ð¢bb5T44TTDTB†Õ÷EdD’ÓävWDçVÖ&W$öd6†FW'2„Æö6F–öâåF—FÆTçVÒÂgVÄçVÔöd6†FW'2’Ð¢bb5T44TTDTB†Õ÷EdD’ÓävWDEdEföÇVÖT–æfò‚gVÄçVÔöeföÇVÖW2ÂgVÅföÇVÖRÂe6–FRÂgVÄçVÔöeF—FÆW2’’’°Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢f÷"…TÄôär’Ò²’ÃÒVÄçVÔöeF—FÆW3²’²²’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†’ÓÒÆö6F–öâåF—FÆTçVÒ’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ¢–b‡VÅTõ2bTõôdÄuõÆ•õF—FÆR’°Ð¢fÆw2ÃÒÔeôu$”TC°Ð¢ÐÐ Ð¢57G&–ær7G#°Ð¢7G"äf÷&ÖB„”E5ôuõD•DÄRÂ’“°Ð Ð¢dU$”e’†Õ÷F—FÆW4ÖVçRäVæDÖVçR†fÆw2Â–B²²Â7G"’“°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õ÷F—FÆW4ÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUõD•DÄU2’ÂÕ÷F—FÆW4ÖVçR“°Ð Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢f÷"…TÄôär’Ò²’ÃÒVÄçVÔöd6†FW'3²’²²’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†’ÓÒÆö6F–öâä6†FW$çVÒ’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ¢–b‡VÅTõ2bTõôdÄuõÆ•ô6†FW"’°Ð¢fÆw2ÃÒÔeôu$”TC°Ð¢ÐÐ Ð¢57G&–ær7G#°Ð¢7G"äf÷&ÖB„”E5ôuô4„DU"Â’“°Ð Ð¢dU$”e’†Õö6†FW'4ÖVçRäVæDÖVçR†fÆw2Â–B²²Â7G"’“°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õö6†FW'4ÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUô4„DU%2’ÂÕö6†FW'4ÖVçR“°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢ÖVçU7F'E&F–õ6V7F–öâ‚“°Ð¢f÷"†6öç7BWFòb6†ææVÂ¢2æÕôEd$6†ææVÇ2’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð Ð¢–b†6†ææVÂävWE&VdçVÖ&W"‚’ÓÒ2æäEd$Æ7D6†ææVÂ’°Ð¢–E6VÆV7FVBÒ–C°Ð¢ÐÐ¢dU$”e’†Õö6†ææVÇ4ÖVçRäVæDÖVçR†fÆw2Â”Eôäd”tDUô¥TÕDõõ5T$•DTÕõ5D%B²6†ææVÂävWE&VdçVÖ&W"‚’Â6æ—F—¦TÖVçTÆ&VÂ†6†ææVÂävWDæÖR‚’’’“°Ð¢–B²³°Ð¢ÐÐ¢ÖVçTVæE&F–õ6V7F–öâ†Õö6†ææVÇ4ÖVçR“°Ð¢FE7V$ÖVçT–e÷76–&ÆR…7G%&W2„”E5ôäd”tDUô4„ääTÅ2’ÂÕö6†ææVÇ4ÖVçR“°Ð¢ÐÐ§ÐÐ Ð¤Etõ$B4Ö–äg&ÖS£¥6WGWæe7G&VÕ6VÆV7E7V$ÖVçR„4ÖVçRb7V$ÖVçRÂT”åB–BÂEtõ$BGu6VÄw&÷WÐ§°Ð¢&ööÂ$FE6W&F÷"ÒfÇ6S°Ð¢Etõ$B6VÆV7FVBÒÓ°Ð¢–çB7G&VÕö6÷VçBÒ°Ð Ð¢WFòFE7G&VÕ6VÆV7Df–ÇFW"Ò²eÒ„46öÕG#Ä”Õ7G&VÕ6VÆV7Câ52’°Ð¢Etõ$B57G&V×3°Ð¢–b‚52ÇÂd”ÄTB‡52Óä6÷VçB‚f57G&V×2’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢&ööÂ$FFVBÒfÇ6S°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð¢Ä4”BÆ6–BÒ°Ð¢–b„d”ÄTB‡52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’Ð¢ÇÂ7¤æÖR’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†Gtw&÷WÒGu6VÄw&÷W’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢òöF"–âæÖR6öÖ–ærg&öÒF†R7Æ—GFW"—2'BöbF†RæÖRÂæ÷B6öÇVÖàÐ¢57G&–æræÖRÒ6æ—F—¦TÖVçTÆ&VÂ„57G&–ær‡7¤æÖR’“°Ð¢ò Ð¢57G&–ærÆ6æÖRÒ57G&–ær†æÖR’äÖ¶TÆ÷vW"‚“°Ð¢–b†Gtw&÷WÓÒ"bbÆ6æÖRäf–æB…õB‚"öfb"’’ãÒ’°Ð¢æÖRäÆöE7G&–ær„”E5ôuôD•4$ÄTB“°Ð¢ÐÐ¢¢ðÐ¢–b†Gtw&÷WÓÒ"bbÆ6–BÒ’°Ð¢57G&–ærÆ6–G7G#°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4TätÄäuTtRÂÆ6–G7G"“°Ð¢æÖRäVæB…õB‚%ÇB"’²Æ6–G7G"“°Ð¢ÐÐ Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b†GtfÆw2’°Ð¢fÆw2ÃÒÔeô4„T4´TC°Ð¢6VÆV7FVBÒ–C°Ð¢ÐÐ Ð¢7G&VÕö6÷VçB²³°Ð Ð¢–b†$FE6W&F÷"’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢$FE6W&F÷"ÒfÇ6S°Ð¢ÐÐ¢$FFVBÒG'VS°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–B²²ÂæÖR’“°Ð¢ÐÐ Ð¢–b†$FFVB’°Ð¢$FE6W&F÷"ÒG'VS°Ð¢ÐÐ¢Ó°Ð Ð¢–b†Õ÷7Æ—GFW%52’°Ð¢FE7G&VÕ6VÆV7Df–ÇFW"†Õ÷7Æ—GFW%52“°Ð¢ÐÐ¢–b‚7G&VÕö6÷VçBbbÕ÷÷F†W%55³Ò’°Ð¢FE7G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò“°Ð¢ÐÐ¢–b‚7G&VÕö6÷VçBbbÕ÷÷F†W%55³Ò’°Ð¢FE7G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò“°Ð¢ÐÐ Ð¢&WGW&â6VÆV7FVC°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öäæe7G&VÕ6VÆV7E7V$ÖVçR…T”åB–BÂEtõ$BGu6VÄw&÷WÐ§°Ð¢–çB7G&VÕö6÷VçBÒ°Ð Ð¢WFò&ö6W757G&VÕ6VÆV7Df–ÇFW"Ò²eÒ„46öÕG#Ä”Õ7G&VÕ6VÆV7Câ52’°Ð¢&ööÂ%6VÆV7FVBÒfÇ6S°Ð Ð¢Etõ$B57G&V×3°Ð¢–b…5T44TTDTB‡52Óä6÷VçB‚f57G&V×2’’’°Ð¢f÷"†–çB’ÒÂ¢Ò57G&V×3²’Â£²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð Ð¢–b„d”ÄTB‡52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’Ð¢ÇÂ7¤æÖR’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†Gtw&÷WÒGu6VÄw&÷W’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢7G&VÕö6÷VçB²³°Ð Ð¢–b‚%6VÆV7FVB’°Ð¢–b†–BÓÒ’°Ð¢52ÓäVæ&ÆR†’ÂÕ5E$TÕ4TÄT5DTä$ÄUôTä$ÄR“°Ð¢%6VÆV7FVBÒG'VS°Ð¢–b†Gu6VÄw&÷WÒ’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢–BÒÓ°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†%6VÆV7FVBbb‡7G&VÕö6÷VçBâ’bbGu6VÄw&÷WÓÒ’°Ð¢6†V6µ6VÆV7FVEf–FVõ7G&VÒ‚“°Ð¢ÐÐ Ð¢&WGW&â%6VÆV7FVC°Ð¢Ó°Ð Ð¢–b†Õ÷7Æ—GFW%52’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷7Æ—GFW%52’’&WGW&ã°Ð¢ÐÐ¢–b‚7G&VÕö6÷VçBbbÕ÷÷F†W%55³Ò’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò’’&WGW&ã°Ð¢ÐÐ¢–b‚7G&VÕö6÷VçBbbÕ÷÷F†W%55³Ò’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò’’&WGW&ã°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öå7G&VÕ6VÆV7B†&ööÂ$f÷'v&BÂEtõ$BGu6VÄw&÷WÐ§°Ð¢54U%B†Gu6VÄw&÷WÓÒÇÂGu6VÄw&÷WÓÒ"“°Ð¢&ööÂ7G&V×5öf÷VæBÒfÇ6S°Ð Ð¢WFò&ö6W757G&VÕ6VÆV7Df–ÇFW"Ò²eÒ„46öÕG#Ä”Õ7G&VÕ6VÆV7Câ52’°Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB‡52Óä6÷VçB‚f57G&V×2’’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢7FC£§fV7F÷#Ç7FC£§GWÆSÄEtõ$BÂ–çBÂÄ4”BÂ57G&–æsãâ7G&V×3°Ð¢6—¦U÷B7W'&VçE6VÂÒ4•¤UôÔƒ°Ð¢f÷"„Etõ$B’Ò²’Â57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢Ä4”BÆ6–BÒ°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð Ð¢–b„d”ÄTB‡52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’Ð¢ÇÂ7¤æÖR’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†Gtw&÷WÒGu6VÄw&÷W’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢7G&V×5öf÷VæBÒG'VS°Ð Ð¢–b†GtfÆw2’°Ð¢7W'&VçE6VÂÒ7G&V×2ç6—¦R‚“°Ð¢ÐÐ¢7G&V×2æV×Æ6Uö&6²†’Â†–çB—7G&V×2ç6—¦R‚’ÂÆ6–BÂ57G&–ær‡7¤æÖR’“°Ð¢ÐÐ Ð¢6—¦U÷B6÷VçBÒ7G&V×2ç6—¦R‚“°Ð¢–b†6÷VçBbb7W'&VçE6VÂÒ4•¤UôÔ‚’°Ð¢6—¦U÷B&WVW7FVBÒ†$f÷'v&Bò7W'&VçE6VÂ²¢7W'&VçE6VÂÒ’R6÷VçC°Ð¢Etõ$B–C°Ð¢–çBG&6¶–æFWƒ°Ð¢Ä4”BÆ6–BÒ°Ð¢57G&–æræÖS°Ð¢7FC£§F–R†–BÂG&6¶–æFW‚ÂÆ6–BÂæÖR’Ò7G&V×2æB‡&WVW7FVB“°Ð¢–b…5T44TTDTB‡52ÓäVæ&ÆR†–BÂÕ5E$TÕ4TÄT5DTä$ÄUôTä$ÄR’’’°Ð¢–b†Gu6VÄw&÷WÓÒÇÂg„vWD6WGF–æw2‚’ædVæ&ÆU7V'F—FÆW2’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂvWE7G&VÔõ4E7G&–ær†æÖRÂÆ6–BÂGu6VÄw&÷W’“°Ð¢ÐÐ¢–b†Gu6VÄw&÷WÓÒ’°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢–b…5T44TTDTB‡52Óä–æfò†–BÂg×BÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢WFFU6VÆV7FVDVF–õ7G&VÔ–æfò‡G&6¶–æFW‚Â×BÂÆ6–B“°Ð¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†Æ6–Bbbg„vWD6WGF–æw2‚’ædVæ&ÆU7V'F—FÆW2’°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4•4óc3”ÄätäÔS"Â7W'&VçE7V$Æær“°Ð¢ÒVÇ6R°Ð¢7W'&VçE7V$ÆæräV×G’‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢&WGW&âG'VS°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð¢Ó°Ð Ð¢–b†Õ÷7Æ—GFW%52’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷7Æ—GFW%52’’&WGW&ã°Ð¢ÐÐ¢–b‚7G&V×5öf÷VæBbbÕ÷÷F†W%55³Ò’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò’’&WGW&ã°Ð¢ÐÐ¢–b‚7G&V×5öf÷VæBbbÕ÷÷F†W%55³Ò’°Ð¢–b‡&ö6W757G&VÕ6VÆV7Df–ÇFW"†Õ÷÷F†W%55³Ò’’&WGW&ã°Ð¢ÐÐ§ÐÐ Ð¤57G&–ær4Ö–äg&ÖS£¤vWE7G&VÔõ4E7G&–ær„57G&–æræÖRÂÄ4”BÆ6–BÂEtõ$BGu6VÄw&÷WÐ§°Ð¢æÖRå&WÆ6R…õB‚%ÇB"’ÂõB‚"Ò"’“°Ð¢57G&–ær4Æ6–C°Ð¢–b†Æ6–BbbÆ6–BÒÄ4”B‚Ó’’°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4TätÄäuTtRÂ4Æ6–B“°Ð¢ÐÐ¢–b‚4Æ6–Bä—4V×G’‚’bb57G&–ær†æÖR’äÖ¶TÆ÷vW"‚’äf–æB„57G&–ær‡4Æ6–B’äÖ¶TÆ÷vW"‚’’Â’°Ð¢æÖR³ÒõB‚"‚"’²4Æ6–B²õB‚"’"“°Ð¢ÐÐ¢57G&–ær7G$ÖW76vS°Ð¢–b†Gu6VÄw&÷WÓÒ’°Ð¢–çBâÒ°Ð¢–b†æÖRäf–æB…õB‚$¢"’’ÓÒ’°Ð¢âÒ#°Ð¢ÐÐ¢7G$ÖW76vRäf÷&ÖB„”E5ôTD”õõ5E$TÒÂæÖRäÖ–B†â’åG&–Ò‚’ävWE7G&–ær‚’“°Ð¢ÒVÇ6R–b†Gu6VÄw&÷WÓÒ"’°Ð¢–çBâÒ°Ð¢–b†æÖRäf–æB…õB‚%3¢"’’ÓÒ’°Ð¢âÒ#°Ð¢ÐÐ¢7G$ÖW76vRäf÷&ÖB„”E5õ5T%D•DÄUõ5E$TÒÂæÖRäÖ–B†â’åG&–Ò‚’ävWE7G&–ær‚’“°Ð¢ÐÐ¢&WGW&â7G$ÖW76vS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGW&V6VçDf–ÆW57V$ÖVçR‚Ð§°Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð¢WFòbÕ%RÒ2äÕ%S°Ð¢Õ%Rå&VDÖVF–†—7F÷'’‚“°Ð Ð¢–b„Õ%RæÆ—7DÖöF–g•6WVVæ6RÓÒ&V6VçDf–ÆW4ÖVçTg&öÔÕ%U6WVVæ6R’°Ð¢&WGW&ã°Ð¢ÐÐ¢&V6VçDf–ÆW4ÖVçTg&öÔÕ%U6WVVæ6RÒÕ%RæÆ—7DÖöF–g•6WVVæ6S°Ð Ð¢4ÖVçRb7V$ÖVçRÒÕ÷&V6VçDf–ÆW4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð¢ Ð¢–b‚2æd¶VW†—7F÷'’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõ$T4TåEôd”ÄU5õ4„õuô„•5Dõ%’Â&W57G"„”E5ô„•5Dõ%•õ4„õr’’“°Ð Ð¢–b„Õ%RävWE6—¦R‚’â’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõ$T4TåEôd”ÄU5ô4ÄT"Â&W57G"„”E5õ$T4TåEôd”ÄU5ô4ÄT"’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"ÂÔeôTä$ÄTB’“°Ð¢T”åB–BÒ”Eõ$T4TåEôd”ÄUõ5D%C°Ð¢f÷"†–çB’Ò²’ÂÕ%RävWE6—¦R‚“²’²²’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð¢–b‚Õ%U¶•Òæfç2ä—4V×G’‚’bbÕ%U¶•Òæfç2ävWD†VB‚’ä—4V×G’‚’’°Ð¢57G&–ærÒÕ%U¶•Òæ7VRä—4V×G’‚’òÕ%U¶•Òæfç2ävWD†VB‚’¢Õ%U¶•Òæ7VS°Ð¢–b‡2æ%W6UF—FÆT–å&V6VçDf–ÆTÆ—7BbbÕ%U¶•ÒçF—FÆRä—4V×G’‚’’°Ð¢57G&–ærF—FÆR„Õ%U¶•ÒçF—FÆR“°Ð¢–b‡F—FÆRävWDÆVæwF‚‚’â’°Ð¢F—FÆRÒF—FÆRäÆVgBƒC’²õB‚'ççâ"’²F—FÆRå&–v‡BƒSr“°Ð¢ÐÐ¢–çBF&vWFÆVâÒSÒF—FÆRävWDÆVæwF‚‚“°Ð¢–b…F…WF–Ç3£¤—5U$Â‡’’°Ð¢–b‡F—FÆRå&–v‡Bƒ’ÓÒÂr’r’°Ð¢òò&ö&&Ç’Ç&VG’6öçF–ç26†÷'GW&ÀÐ¢ÒF—FÆS°Ð¢ÒVÇ6R°Ð¢57G&–ær6†÷'GW&ÂÒ6†÷'FVåU$Â‡ÂF&vWFÆVâÂG'VR“°Ð¢äf÷&ÖB…õB‚"W2‚W2’"’Â7FF–5ö67CÄÅ5u5E#â‡F—FÆR’Â7FF–5ö67CÄÅ5u5E#â‡6†÷'GW&Â’“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢57G&–ærfâÒF…WF–Ç3£¥7G&—F„÷%W&Â‡“°Ð¢–b†fâävWDÆVæwF‚‚’âF&vWFÆVâ’²òò–bf–ÆRæÖR—2FöòÆöærÂ7WBÖ–FFÆR'BàÐ¢–çBÂÒfâävWDÆVæwF‚‚“°Ð¢fâäf÷&ÖB…õB‚"W7ççâW2"’Â7FF–5ö67CÄÅ5u5E#â†fâäÆVgB†Âò"Ò"²†ÂR"’’’Â7FF–5ö67CÄÅ5u5E#â†fâå&–v‡B†Âò"Ò’’“°Ð¢ÐÐ¢äf÷&ÖB…õB‚"W2‚W2’"’Â7FF–5ö67CÄÅ5u5E#â‡F—FÆR’Â7FF–5ö67CÄÅ5u5E#â†fâ’“°Ð¢ÐÐ¢ÐÐ¢VÇ6R°Ð¢–b…F…WF–Ç3£¤—5U$Â‡’’°Ð¢Ò6†÷'FVåU$Â‡ÂS“°Ð¢ÐÐ¢–b‡ävWDÆVæwF‚‚’âS’°Ð¢äf÷&ÖB…õB‚"W7ççâW2"’Â7FF–5ö67CÄÅ5u5E#â‡äÆVgBƒc’’Â7FF–5ö67CÄÅ5u5E#â‡å&–v‡Bƒƒr’’“°Ð¢ÐÐ¢ÐÐ¢Ò6æ—F—¦TÖVçTÆ&VÂ‡Â“²òöÇ&VG’6†÷'FVæVB&÷fRÂ–âv’F†B¶VW2F†RW‡FVç6–öâf—6–&ÆPÐ¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–BÂ’“°Ð¢ÒVÇ6R°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ¢–B²³°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWff÷&—FW57V$ÖVçR‚Ð§°Ð¢4ÖVçRb7V$ÖVçRÒÕöff÷&—FW4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eôddõ$•DU5ôDBÂ&W57G"„”E5ôddõ$•DU5ôDB’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eôddõ$•DU5ôõ$tä•¤RÂ&W57G"„”E5ôddõ$•DU5ôõ$tä•¤R’’“°Ð Ð¢T”åBäÆ7Dw&÷W7F'BÒ7V$ÖVçRävWDÖVçT—FVÔ6÷VçB‚“°Ð¢T”åB–BÒ”Eôddõ$•DU5ôd”ÄUõ5D%C°Ð¢4FÄÆ—7CÄ57G&–æsâfg3°Ð¢g„vWD6WGF–æw2‚’ävWDfb„deôd”ÄRÂfg2“°Ð¢õ4•D”ôâ÷2Òfg2ävWD†VE÷6—F–öâ‚“°Ð Ð¢v†–ÆR‡÷2’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð Ð¢57G&–ære÷7G"Òfg2ävWDæW‡B‡÷2“°Ð Ð¢f–ÆTff÷&—FRfc°Ð¢dU$”e’„f–ÆTff÷&—FS£¥G'•'6R†e÷7G"Âfb’“²ò÷'6R&Vf÷&R6æ—F—¦–ærÂF†RW66–ær—2æ÷B'BöbF†Rf÷&Ö@Ð Ð¢e÷7G"ÒfbäæÖS°Ð¢–b‚e÷7G"ä—4V×G’‚’’°Ð¢e÷7G"Ò6æ—F—¦TÖVçTÆ&VÂ†e÷7G"“°Ð¢ÐÐ Ð¢57G&–ær7G"ÒfbåFõ7G&–ær‚“°Ð¢–b‚7G"ä—4V×G’‚’’°Ð¢e÷7G"äVæDf÷&ÖB…õB‚%ÇBW2"’Â7G"ävWE7G&–ær‚’“°Ð¢ÐÐ Ð¢–b‚e÷7G"ä—4V×G’‚’’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–BÂe÷7G"’“°Ð¢ÐÐ Ð¢–B²³°Ð¢–b†–Bâ”Eôddõ$•DU5ôd”ÄUôTäB’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢–b†–Bâ”Eôddõ$•DU5ôd”ÄUõ5D%B’°Ð¢dU$”e’‡7V$ÖVçRä–ç6W'DÖVçR†äÆ7Dw&÷W7F'BÂÔeõ4U$Dõ"ÂÔeôTä$ÄTBÂÔeô%•õ4•D”ôâ’“°Ð¢ÐÐ Ð¢äÆ7Dw&÷W7F'BÒ7V$ÖVçRävWDÖVçT—FVÔ6÷VçB‚“°Ð Ð¢–BÒ”Eôddõ$•DU5ôEdEõ5D%C°Ð¢2ävWDfb„deôEdBÂfg2“°Ð¢÷2Òfg2ävWD†VE÷6—F–öâ‚“°Ð Ð¢v†–ÆR‡÷2’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð Ð¢57G&–ær7G"Òfg2ävWDæW‡B‡÷2“°Ð Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð¢W‡ÆöFTW62‡7G"Â6ÂÂõB‚s²r’Â"“°Ð Ð¢7G"Ò6Âå&VÖ÷fT†VB‚“°Ð Ð¢–b‚6Âä—4V×G’‚’’°Ð¢òòDôDðÐ¢ÐÐ Ð¢–b‚7G"ä—4V×G’‚’’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–BÂ6æ—F—¦TÖVçTÆ&VÂ‡7G"’’“°Ð¢ÐÐ Ð¢–B²³°Ð¢–b†–Bâ”Eôddõ$•DU5ôEdEôTäB’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ Ð¢–b†–Bâ”Eôddõ$•DU5ôEdEõ5D%B’°Ð¢dU$”e’‡7V$ÖVçRä–ç6W'DÖVçR†äÆ7Dw&÷W7F'BÂÔeõ4U$Dõ"ÂÔeôTä$ÄTBÂÔeô%•õ4•D”ôâ’“°Ð¢ÐÐ Ð¢äÆ7Dw&÷W7F'BÒ7V$ÖVçRävWDÖVçT—FVÔ6÷VçB‚“°Ð Ð¢–BÒ”Eôddõ$•DU5ôDUd”4Uõ5D%C°Ð Ð¢2ävWDfb„deôDUd”4RÂfg2“°Ð Ð¢÷2Òfg2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢T”åBfÆw2ÒÔeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTC°Ð Ð¢57G&–ær7G"Òfg2ävWDæW‡B‡÷2“°Ð Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð¢W‡ÆöFTW62‡7G"Â6ÂÂõB‚s²r’Â"“°Ð Ð¢7G"Ò6Âå&VÖ÷fT†VB‚“°Ð Ð¢–b‚7G"ä—4V×G’‚’’°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR†fÆw2Â–BÂ6æ—F—¦TÖVçTÆ&VÂ‡7G"’’“°Ð¢ÐÐ Ð¢–B²³°Ð¢–b†–Bâ”Eôddõ$•DU5ôDUd”4UôTäB’°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥6WGW6†FW'57V$ÖVçR‚Ð§°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð Ð¢4ÖVçRb7V$ÖVçRÒÕ÷6†FW'4ÖVçS°Ð¢òòV×G’F†RÖVçPÐ¢v†–ÆR‡7V$ÖVçRå&VÖ÷fTÖVçRƒÂÔeô%•õ4•D”ôâ’“°Ð Ð¢–b‚‡2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5ôUe%ô5U5DôÒÇÂ2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5õ5”ä0Ð¢ÇÂ2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5õdÕ#•$TäDU$ÄU52ÇÂ2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5ôÔEe"ÇÂ2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5ôÕ5e"’’°Ð¢&WGW&âfÇ6S°Ð¢Ò Ð Ð¢7V$ÖVçRäVæDÖVçR„Ôeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõ$U4•¤Uõ4„DU%5õDôttÄRÂ&W57G"„”E5õ$U4•¤Uõ4„DU%5õDôttÄR’“°Ð¢7V$ÖVçRäVæDÖVçR„Ôeô%”4ôÔÔäBÂÔeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõõ5E4•¤Uõ4„DU%5õDôttÄRÂ&W57G"„”E5õõ5E4•¤Uõ4„DU%5õDôttÄR’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõ4„DU%5õ4TÄT5BÂ&W57G"„”E5õ4„DU%5õ4TÄT5B’’“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂ”Eõd”UuôDT%Tu4„DU%2Â&W57G"„”E5õ4„DU%5ôDT%Tr’’“°Ð Ð¢WFò&W6WG2Ò2æÕõ6†FW'2ävWE&W6WG2‚“°Ð¢–b‚&W6WG2æV×G’‚’’°Ð¢57G&–ær7W'&VçC°Ð¢&ööÂ6VÆV7FVBÒ2æÕõ6†FW'2ävWD7W'&VçE&W6WDæÖR†7W'&VçB“°Ð¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ4U$Dõ"’“°Ð¢T”åBä”BÒ”Eõ4„DU%5õ$U4UE5õ5D%C°Ð¢f÷"†6öç7BWFòb—"¢&W6WG2’°Ð¢–b†ä”Bâ”Eõ4„DU%5õ$U4UE5ôTäB’°Ð¢òòFöòÖç’&W6WG0Ð¢54U%B„dÅ4R“°Ð¢'&V³°Ð¢ÐÐ¢dU$”e’‡7V$ÖVçRäVæDÖVçR„Ôeõ5E$”ärÂÔeôTä$ÄTBÂä”BÂ6æ—F—¦TÖVçTÆ&VÂ‡—"æf—'7B’’“°Ð¢–b‡6VÆV7FVBbb—"æf—'7BÓÒ7W'&VçB’°Ð¢dU$”e’‡7V$ÖVçRä6†V6´ÖVçU&F–ô—FVÒ†ä”BÂä”BÂä”BÂÔeô%”4ôÔÔäB’“°Ð¢6VÆV7FVBÒfÇ6S°Ð¢ÐÐ¢ä”B²³°Ð¢ÐÐ¢ÐÐ¢&WGW&âG'VS°Ð§ÐÐ Ð¢òòòòòòòòòòòòðÐ Ð§fö–B4Ö–äg&ÖS£¥6WDÇv—4öåF÷†–çB”öåF÷Ð§°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b‚—4gVÆÅ67&VVäÖöFR‚’’°Ð¢6öç7B5væB¢–ç6W'DgFW"ÒçVÆÇG#°Ð Ð¢–b†”öåF÷ÓÒ’°Ð¢òòvRöæÇ’vçBFòF—6&ÆR$öâF÷"öæ6R6òF†@Ð¢òòvRFöâwB–çFW&fW&Rv—F‚÷F†W"v–æF÷rÖævW Ð¢–b‡2æ”öåF÷ÇÂÇv—4öåF÷¤÷&FW$–æ—F–Æ—¦VB’°Ð¢–ç6W'DgFW"ÒgvæDæõF÷Ö÷7C°Ð¢Çv—4öåF÷¤÷&FW$–æ—F–Æ—¦VBÒG'VS°Ð¢ÐÐ¢ÒVÇ6R–b†”öåF÷ÓÒ’°Ð¢–ç6W'DgFW"ÒgvæEF÷Ö÷7C°Ð¢ÒVÇ6R–b†”öåF÷ÓÒ"’°Ð¢–ç6W'DgFW"Ò„vWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’ògvæEF÷Ö÷7B¢gvæDæõF÷Ö÷7C°Ð¢ÒVÇ6R²òò–b†”öåF÷ÓÒ2Ð¢–ç6W'DgFW"Ò„vWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ærbbÕödVF–ôöæÇ’’ògvæEF÷Ö÷7B¢gvæDæõF÷Ö÷7C°Ð¢ÐÐ Ð¢–b‡–ç6W'DgFW"’°Ð¢6WEv–æF÷u÷2‡–ç6W'DgFW"ÂÂÂÂÂ5uôäôÔõdRÂ5uôäõ4•¤RÂ5uôäô5D•dDR“°Ð¢ÐÐ¢ÐÐ Ð¢2æ”öåF÷Ò”öåF÷°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥v–æF÷tW‡V7FVDöåF÷‚’°Ð¢&WGW&â„g„vWD6WGF–æw2‚’æ”öåF÷ÓÒÇÀÐ¢„g„vWD6WGF–æw2‚’æ”öåF÷ÓÒ"bbvWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’ÇÀÐ¢„g„vWD6WGF–æw2‚’æ”öåF÷ÓÒ2bbvWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ærbbÕödVF–ôöæÇ’’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤FEFW‡E75F‡'Tf–ÇFW"‚Ð§°Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢–b‚—57Æ—GFW"‡$b’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢46öÕG#Ä•–ãâ–åFó°Ð¢ÕôÔTD”õE•R×C°Ð¢–b…5T44TTDTB‡–âÓä6öææV7FVEFò‚g–åFò’’bb–åFðÐ¢bb5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’Ð¢bb†×BæÖ¦÷'G—RÓÒÔTD”E•UõFW‡BÇÂ×BæÖ¦÷'G—RÓÒÔTD”E•Uõ7V'F—FÆR’’°Ð¢–ç6W'EFW‡E75F‡'Tf–ÇFW"‡$bÂ–âÂ–åFò“°Ð¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¤–ç6W'EFW‡E75F‡'Tf–ÇFW"„”&6Tf–ÇFW"¢$bÂ•–â¢–âÂ•–â¢–åFòÐ§°Ð¢…$U5TÅB‡#°Ð¢46öÕ•G#Ä”&6Tf–ÇFW#âEDbÒDT%TuôäUr5FW‡E75F‡'Tf–ÇFW"‡F†—2“°Ð¢57G&–æuræÖS°Ð¢æÖRäf÷&ÖB„Â%FW‡E75F‡'RW"Â7FF–5ö67CÇfö–B£â‡EDb’“°Ð¢–b„d”ÄTB†‡"ÒÕ÷t"ÓäFDf–ÇFW"‡EDbÂæÖR’’’°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢ôf–ÇFW%7FFRg2ÒvWDÖVF–7FFR‚“°Ð¢–b†g2ÓÒ7FFUõ'Vææ–ærÇÂg2ÓÒ7FFUõW6VB’°Ð¢ÖVF–6öçG&öÅ7F÷‡G'VR“°Ð¢ÐÐ Ð¢‡"Ò–åFòÓäF—66öææV7B‚“°Ð¢‡"Ò–âÓäF—66öææV7B‚“°Ð Ð¢–b„d”ÄTB†‡"ÒÕ÷t"Óä6öææV7DF—&V7B‡–âÂvWDf—'7E–â‡EDbÂ”äD•%ô”åUB’ÂçVÆÇG"’Ð¢ÇÂd”ÄTB†‡"ÒÕ÷t"Óä6öææV7DF—&V7B„vWDf—'7E–â‡EDbÂ”äD•%ôõUEUB’Â–åFòÂçVÆÇG"’’’°Ð¢‡"ÒÕ÷t"Óä6öææV7DF—&V7B‡–âÂ–åFòÂçVÆÇG"“°Ð¢ÒVÇ6R°Ð¢7V'F—FÆT–çWB7V$–çWB„46öÕ•G#Ä•7V%7G&VÓâ‡EDb’Â$b“°Ð¢Õ÷7V%7G&V×2äFEF–Â‡7V$–çWB“°Ð¢ÐÐ Ð¢–b†g2ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅ'Vâ‚“°Ð¢ÒVÇ6R–b†g2ÓÒ7FFUõW6VB’°Ð¢ÖVF–6öçG&öÅW6R‚“°Ð¢ÐÐ Ð¢&WGW&â‡#°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤ÆöE7V'F—FÆR„57G&–ærfâÂ7V'F—FÆT–çWB¢7V$–çWBò£ÒçVÆÇG"¢òÂ&ööÂ$WFôÆöBò£ÒfÇ6R¢òÐ§°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢46öÕ•G#Ä•7V%7G&VÓâ7V%7G&VÓ°Ð Ð¢–b‚2ä—4•5$WFôÆöDVæ&ÆVB‚’bb„f–æDf–ÇFW"„4Å4”Eõe4f–ÇFW"ÂÕ÷t"’ÇÂf–æDf–ÇFW"„4Å4”Eõ‡•7V$f–ÇFW"ÂÕ÷t"’’’°Ð¢òò&WfVçB•5"g&öÒÆöF–ær–be4f–ÇFW"—2Ç&VG’–âw&‚àÐ¢òòDôDó¢7W÷'Be4f–ÇFW"æF—fVÇ’‡6VRF–6¶WB3C#"Ð¢òòæ÷FRF†BF†—2FöW6âwBffV7B•5"WFòÖÆöF–ær–bç’7V"&VæFW&W"f÷&6RÆöF–ær—G6VÆb–çFòF†Rw&‚àÐ¢òòe4f–ÇFW"Æ–¶Rf–ÇFW'26â&R&Æö6¶VBv†Vâ'V–ÆF–ærF†Rw&‚æB•5"WFòÖÆöF–ær—2Væ&ÆVB'WB6öÖPÐ¢òòW6W'2FöâwBvçBF†BàÐ¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRbb2ædF—6&ÆT–çFW&æÅ7V'F—FÆW2bbf–æDf–ÇFW"…õ÷WV–Föb„5FW‡E75F‡'Tf–ÇFW"’ÂÕ÷t"’’°Ð¢òòFBFW‡E75F‡'Rf–ÇFW"–b—B—6âwBÇ&VG’–âF†Rw&‚â†’æR•5"†6âwB&VVâÆöFVB&Vf÷&RÐ¢òòF†—2v–ÆÂÆöBÆÂVÖ&VFFVB7V'F—FÆRG&6·2v†VâW6W"G&–vvW'2•5"†ÆöBW‡FW&æÂ7V'F—FÆRf–ÆR’f÷"F†Rf—'7BF–ÖRàÐ¢FEFW‡E75F‡'Tf–ÇFW"‚“°Ð¢ÐÐ Ð¢57G&–ærf–FVôæÖS°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢f–FVôæÖRÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‚“°Ð¢ÐÐ Ð¢57G&–ærW‡BÒ5F‚†fâ’ävWDW‡FVç6–öâ‚’äÖ¶TÆ÷vW"‚“°Ð Ð¢–b‚7V%7G&VÒbb†W‡BÓÒõB‚"æ–G‚"’ÇÂ$WFôÆöBbbW‡BÓÒõB‚"ç7V""’’’°Ð¢4WFõG#Ä5fö%7V$f–ÆSâe4b„DT%TuôäUr5fö%7V$f–ÆR‚fÕö757V$Æö6²’“°Ð¢–b‡e4bbbe4bÓä÷Vâ†fâ’bbe4bÓävWE7G&VÔ6÷VçB‚’â’°Ð¢7V%7G&VÒÒe4bäFWF6‚‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚7V%7G&VÒbbW‡BÒõB‚"æ–G‚"’bbW‡BÒõB‚"ç7W"’’°Ð¢4WFõG#Ä5&VæFW&VEFW‡E7V'F—FÆSâ%E2„DT%TuôäUr5&VæFW&VEFW‡E7V'F—FÆR‚fÕö757V$Æö6²’“°Ð¢–b‡%E2’°Ð¢–b‡%E2Óä÷Vâ†fâÂDTdTÅEô4„%4UBÂõB‚""’Âf–FVôæÖR’bb%E2ÓävWE7G&VÔ6÷VçB‚’â’°Ð¢6–bU4UôÄ”$50Ð¢–b‡%E2ÓæÕôÆ–&746öçFW‡Bä—4Æ–&747F—fR‚’’°Ð¢%E2ÓæÕôÆ–&746öçFW‡Bå6WDf–ÇFW$w&‚†Õ÷t"“°Ð¢ÐÐ¢6VæF–`Ð¢7V%7G&VÒÒ%E2äFWF6‚‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b‚7V%7G&VÒ’°Ð¢4WFõG#Ä5u57V$f–ÆSâ4b„DT%TuôäUr5u57V$f–ÆR‚fÕö757V$Æö6²’“°Ð¢–b‡4bbb4bÓä÷Vâ†fâÂõB‚""’Âf–FVôæÖR’bb4bÓävWE7G&VÔ6÷VçB‚’â’°Ð¢7V%7G&VÒÒ4bäFWF6‚‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b‡7V%7G&VÒ’°Ð¢7V'F—FÆT–çWB7V$–çWB‡7V%7G&VÒ“°Ð¢ÕôW‡FW&æÅ7V'7G&V×2çW6…ö&6²‡7V%7G&VÒ“°Ð¢Õ÷7V%7G&V×2äFEF–Â‡7V$–çWB“°Ð Ð¢òòFV×÷&&–Ç’ÆöBföçG2g&öÒtföçG2rföÆFW"Ò&Vv–àÐ¢57G&–ærF‚ÒF…WF–Ç3£¤F—$æÖR†fâ’²Â%ÅÆföçG5ÅÂ#°Ð¢W‡FVæDÖ…F„ÆVæwF„–dæVVFVB‡F‚“°Ð Ð¢–bƒ£¥F„—4F—&V7F÷'’‡F‚’’°Ð¢t”ã3%ôd”äEôDDfBÒ³Ó°Ð¢„äDÄR„f–æC°Ð¢ Ð¢„f–æBÒf–æDf—'7Df–ÆR‡F‚²Â"¢ã÷Cò"ÂffB“°Ð¢–b†„f–æBÒ”ådÄ”Eô„äDÄUõdÅTR’°Ð¢Fò°Ð¢57G&–æurW‡BÒvWDf–ÆTW‡B†fBæ4f–ÆTæÖR“°Ð¢–b†W‡BÓÒ"çGFb"ÇÂW‡BÓÒ"æ÷Fb"ÇÂW‡BÓÒ"çGF2"’°Ð¢ÕôföçD–ç7FÆÆW"ä–ç7FÆÅFV×föçDf–ÆR‡F‚²fBæ4f–ÆTæÖR“°Ð¢ÐÐ¢Òv†–ÆR„f–æDæW‡Df–ÆR†„f–æBÂffB’“°Ð¢ Ð¢f–æD6Æ÷6R†„f–æB“°Ð¢ÐÐ¢ÐÐ¢òòFV×÷&&–Ç’ÆöBföçG2g&öÒtföçG2rföÆFW"ÒVæ@Ð Ð¢–b‚Õ÷÷4f—'7DW‡E7V"’°Ð¢Õ÷÷4f—'7DW‡E7V"ÒÕ÷7V%7G&V×2ävWEF–Å÷6—F–öâ‚“°Ð¢ÐÐ Ð¢–b‡7V$–çWB’°Ð¢§7V$–çWBÒ7V$–çWC°Ð¢ÐÐ Ð¢–b‚$WFôÆöB’°Ð¢Õ÷væEÆ–Æ—7D&"äFE7V'F—FÆUFô7W'&VçB†fâ“°Ð¢–b‡2æd¶VW†—7F÷'’’°Ð¢2äÕ%RäFE7V%Fô7W'&VçB†fâ“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&â7V%7G&VÓ°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤ÆöE7V'F—FÆR„5–÷WGV&TDÄ–ç7Fæ6S£¥”DÅ7V$–æfòb7V"’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢46öÕ•G#Ä•7V%7G&VÓâ7V%7G&VÓ°Ð¢4FÄÆ—7CÄ57G&–æsâ&VfW&Æ—7C°Ð¢–b‚2ç5”DÅ7V'5&VfW&Væ6Rä—4V×G’‚’’°Ð¢–b‡2ç5”DÅ7V'5&VfW&Væ6Räf–æB…õB‚rÂr’’ÒÓ’°Ð¢W‡ÆöFTÖ–â‡2ç5”DÅ7V'5&VfW&Væ6RÂ&VfW&Æ—7BÂrÂr“°Ð¢ÒVÇ6R°Ð¢W‡ÆöFTÖ–â‡2ç5”DÅ7V'5&VfW&Væ6RÂ&VfW&Æ—7BÂrr“°Ð¢ÐÐ¢ÐÐ¢–b‚&VfW&Æ—7Bä—4V×G’‚’bb5–÷WGV&TDÄ–ç7Fæ6S£¦—5&VfW"‡&VfW&Æ—7BÂ7V"æÆær’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b‚2ä—4•5$WFôÆöDVæ&ÆVB‚’bb„f–æDf–ÇFW"„4Å4”Eõe4f–ÇFW"ÂÕ÷t"’ÇÂf–æDf–ÇFW"„4Å4”Eõ‡•7V$f–ÇFW"ÂÕ÷t"’’’°Ð¢òò&WfVçB•5"g&öÒÆöF–ær–be4f–ÇFW"—2Ç&VG’–âw&‚àÐ¢òòDôDó¢7W÷'Be4f–ÇFW"æF—fVÇ’‡6VRF–6¶WB3C#"Ð¢òòæ÷FRF†BF†—2FöW6âwBffV7B•5"WFòÖÆöF–ær–bç’7V"&VæFW&W"f÷&6RÆöF–ær—G6VÆb–çFòF†Rw&‚àÐ¢òòe4f–ÇFW"Æ–¶Rf–ÇFW'26â&R&Æö6¶VBv†Vâ'V–ÆF–ærF†Rw&‚æB•5"WFòÖÆöF–ær—2Væ&ÆVB'WB6öÖPÐ¢òòW6W'2FöâwBvçBF†BàÐ¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRbb2ædF—6&ÆT–çFW&æÅ7V'F—FÆW2bbf–æDf–ÇFW"…õ÷WV–Föb„5FW‡E75F‡'Tf–ÇFW"’ÂÕ÷t"’’°Ð¢òòFBFW‡E75F‡'Rf–ÇFW"–b—B—6âwBÇ&VG’–âF†Rw&‚â†’æR•5"†6âwB&VVâÆöFVB&Vf÷&RÐ¢òòF†—2v–ÆÂÆöBÆÂVÖ&VFFVB7V'F—FÆRG&6·2v†VâW6W"G&–vvW'2•5"†ÆöBW‡FW&æÂ7V'F—FÆRf–ÆR’f÷"F†Rf—'7BF–ÖRàÐ¢FEFW‡E75F‡'Tf–ÇFW"‚“°Ð¢ÐÐ Ð¢4WFõG#Ä5&VæFW&VEFW‡E7V'F—FÆSâ%E2„DT%TuôäUr5&VæFW&VEFW‡E7V'F—FÆR‚fÕö757V$Æö6²’“°Ð¢–b‡%E2’°Ð¢&ööÂ÷VæVBÒfÇ6S°Ð¢–b‚7V"çW&Âä—4V×G’‚’’°Ð¢7V'F—FÆW5&÷f–FW'5WF–Ç3£§7G&–ætÖ7G&Ö·Ó°Ð¢Etõ$BGu7FGW46öFS°Ð¢5C$4FVÒ‡7V"çW&Â“°Ð¢7FC£§7G&–ærFVÓ"‡FVÒ“°Ð¢7FC£§7G&–ærFF‚""“°Ð¢7V'F—FÆW5&÷f–FW'5WF–Ç3£¥7G&–ætF÷væÆöB‡FVÓ"Â7G&ÖÂFFÂG'VRÂfGu7FGW46öFR“°Ð¢–b†Gu7FGW46öFRÒ#’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢–b‡7V"æW‡Bä—4V×G’‚’’°Ð¢–çBÓ"‡7V"çW&Âå&WfW'6Tf–æB…õB‚sòr’’“°Ð¢–çBÓ2‡7V"çW&Âå&WfW'6Tf–æB…õB‚r2r’’“°Ð¢–çBÒÒÓ°Ð¢–b†Ó"âÓbbÓ2âÓ’ÒÒ7FC£¦Ö–â†Ó"ÂÓ2“°Ð¢VÇ6R–b†Ó"âÓ’ÒÒÓ#°Ð¢VÇ6R–b†Ó2âÓ’ÒÒÓ3°Ð¢57G&–ærFV×‡7V"çW&Â“°Ð¢–b†Òâ’FV×Ò7V"çW&ÂäÆVgB†Ò“°Ð¢ÒÒFV×å&WfW'6Tf–æB…õB‚râr’“°Ð¢–b†ÒãÒ’7V"æW‡BÒFV×äÖ–B†Ò²“°Ð¢ÐÐ¢57G&–ærÆæwBÒ7V"æ—4WFöÖF–46F–öç2ò7V"æÆær²õB‚%´WFöÖF–5Ò"’¢7V"æÆæs°Ð¢÷VæVBÒ%E2Óä÷Vâ‚„%•DR¢–FFæ5÷7G"‚’Â†–çB–FFæÆVæwF‚‚’ÂDTdTÅEô4„%4UBÂõB‚%–÷WGV&TDÂ"’ÂÆæwBÂ7V"æW‡B“°Ð¢ÒVÇ6R–b‚7V"æFFä—4V×G’‚’’°Ð¢57G&–ærÆæwBÒ7V"æ—4WFöÖF–46F–öç2ò7V"æÆær²õB‚%´WFöÖF–5Ò"’¢7V"æÆæs°Ð¢÷VæVBÒ%E2Óä÷Vâ‡7V"æFFÂ5FW‡Df–ÆS£¦Væ3£¥UDc‚ÂDTdTÅEô4„%4UBÂõB‚%–÷WGV&TDÂ"’ÂÆæwBÂ7V"æW‡B“²òòFòæ÷BÖöF–g’6†'6WBÂæ÷r—Bw&ö·2v—F‚Væ–6öFR6†"àÐ¢ÐÐ¢–b†÷VæVBbb%E2ÓävWE7G&VÔ6÷VçB‚’â’°Ð¢6–bU4UôÄ”$50Ð¢–b‡%E2ÓæÕôÆ–&746öçFW‡Bä—4Æ–&747F—fR‚’’°Ð¢%E2ÓæÕôÆ–&746öçFW‡Bå6WDf–ÇFW$w&‚†Õ÷t"“°Ð¢ÐÐ¢6VæF–`Ð¢7V%7G&VÒÒ%E2äFWF6‚‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b‡7V%7G&VÒ’°Ð¢7V'F—FÆT–çWB7V$–çWB‡7V%7G&VÒ“°Ð¢ÕôW‡FW&æÅ7V'7G&V×2çW6…ö&6²‡7V%7G&VÒ“°Ð¢Õ÷7V%7G&V×2äFEF–Â‡7V$–çWB“°Ð Ð¢–b‚Õ÷÷4f—'7DW‡E7V"’°Ð¢Õ÷÷4f—'7DW‡E7V"ÒÕ÷7V%7G&V×2ävWEF–Å÷6—F–öâ‚“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&â7V%7G&VÓ°Ð§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð¦&ööÂ4Ö–äg&ÖS£¥6WE7V'F—FÆR†–çB’Â&ööÂ$—4öfg6WBò£ÒfÇ6R¢òÂ&ööÂ$F—7Æ”ÖW76vRò£ÒfÇ6R¢òÐ§°Ð¢–b‚Õ÷4’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤4Äõ4”är’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢7V'F—FÆT–çWB¢7V$–çWBÒçVÆÇG#°Ð¢–b†Õö•&VÆöE7V$–G‚ãÒ’°Ð¢7V$–çWBÒvWE7V'F—FÆT–çWB†Õö•&VÆöE7V$–G‚“°Ð¢–b‡7V$–çWB’°Ð¢’ÒÕö•&VÆöE7V$–Gƒ°Ð¢ÐÐ¢Õö•&VÆöE7V$–G‚ÒÓ°Ð¢ÐÐ Ð¢–b‚7V$–çWB’°Ð¢7V$–çWBÒvWE7V'F—FÆT–çWB†’Â$—4öfg6WB“°Ð¢ÐÐ Ð¢&ööÂ7V66W72ÒfÇ6S°Ð Ð¢–b‡7V$–çWB’°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBÓç6÷W&6Tf–ÇFW"’°Ð¢Etõ$BGtfÆw3°Ð¢Ä4”BÆ6–BÒ°Ð¢–b„d”ÄTB‡54bÓä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂfÆ6–BÂçVÆÇG"ÂgæÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢GtfÆw2Ò°Ð¢ÐÐ¢–b†Æ6–Bbb2ædVæ&ÆU7V'F—FÆW2’°Ð¢7W'&VçE7V$ÆærÒ•4ôÆæs£¤Ä4”EFô•4óc3“"†Æ6–B“°Ð¢ÒVÇ6R°Ð¢7W'&VçE7V$ÆæräV×G’‚“°Ð¢ÐÐ Ð¢òòVæ&ÆRF†RG&6²öæÇ’–b—B—6âwBÇ&VG’F†RöæÇ’6VÆV7FVBG&6²–âF†Rw&÷W Ð¢–b‚†GtfÆw2bÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢54bÓäVæ&ÆR†’ÂÕ5E$TÕ4TÄT5DTä$ÄUôTä$ÄR“°Ð¢ÐÐ¢’Ò°Ð¢ÐÐ¢°Ð¢òòÕö757V$Æö6²6†÷VÆFâwB&RÆö6¶VBv†VâW6–ær”Õ7G&VÕ6VÆV7C£¤Væ&ÆR÷"6WE7V'F—FÆPÐ¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢7V$–çWBÓç7V%7G&VÒÓå6WE7G&VÒ†’“°Ð¢ÐÐ¢6WE7V'F—FÆR‚§7V$–çWBÂG'VR“°Ð Ð¢–b‚æÖR’°Ð¢Ä4”BÆ6–BÒ°Ð¢7V$–çWBÓç7V%7G&VÒÓävWE7G&VÔ–æfòƒÂgæÖRÂfÆ6–B“°Ð¢–b†Æ6–Bbb2ædVæ&ÆU7V'F—FÆW2’°Ð¢7W'&VçE7V$ÆærÒ•4ôÆæs£¤Ä4”EFô•4óc3“"†Æ6–B“°Ð¢ÒVÇ6R°Ð¢7W'&VçE7V$ÆæräV×G’‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b†$F—7Æ”ÖW76vRbbæÖR’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂvWE7G&VÔõ4E7G&–ær„57G&–ær‡æÖR’ÂÄ4”B‚Ó’Â"’“°Ð¢ÐÐ¢7V66W72ÒG'VS°Ð¢ÐÐ Ð¢–b‡7V66W72bb2æd¶VW†—7F÷'’bb2æ%&VÖVÖ&W%G&6µ6VÆV7F–öâ’°Ð¢2äÕ%RåWFFT7W'&VçE7V'F—FÆUG&6²„vWE6VÆV7FVE7V'F—FÆUG&6´–æFW‚‚’“°Ð¢ÐÐ¢&WGW&â7V66W73°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFU7V'F—FÆT6öÆ÷$–æfò‚Ð§°Ð¢–b‚—57FFTÆöFVB‚’ÇÂÕ÷4 Ð¢ÇÂ‚Õ÷7W'&VçE7V$–çWBç7V%7G&VÒbbÕ÷6V6öæF'•7V$–çWBç7V%7G&VÒ’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òò7F÷&Rf–FVòÖVF–G—RÂ6ò6öÆ÷'76R–æf÷&ÖF–öâ6â&RW‡G&7FVBv†Vâ&W6Vç@Ð¢”&6Tf–ÇFW"¢$bÒf–æDf–ÇFW"„uT”EôÄef–FVòÂÕ÷t"“°Ð¢–b‡$b’°Ð¢46öÕG#Ä•–ãâ–âÒvWDf—'7E–â‡$bÂ”äD•%ôõUEUB“°Ð¢–b‡–â’°Ð¢ÕôÔTD”õE•R×C°Ð¢–b…5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢Õ÷4Óå6WEf–FVôÖVF–G—R„4ÖVF–G—R†×B’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢46öÕ•G#Ä•7V%&VæFW$÷F–öç3â5$òÒÕ÷4°Ð Ð¢Åu5E"—WdÖG&—‚ÒçVÆÇG#°Ð¢–çBäÆVã°Ð¢–b†Õ÷Õe$’’°Ð¢Õ÷Õe$’ÓävWE7G&–ær‚'—WdÖG&—‚"Âg—WdÖG&—‚ÂfäÆVâ“°Ð¢ÒVÇ6R–b‡5$ò’°Ð¢5$òÓävWE7G&–ær‚'—WdÖG&—‚"Âg—WdÖG&—‚ÂfäÆVâ“°Ð¢ÐÐ Ð¢–çBF&vWD&Æ6´ÆWfVÂÒÂF&vWEv†—FTÆWfVÂÒ#SS°Ð¢–b†Õ÷Õe%2’°Ð¢Õ÷Õe%2Óå6WGF–æw4vWD–çFVvW"„Â$&Æ6²"ÂgF&vWD&Æ6´ÆWfVÂ“°Ð¢Õ÷Õe%2Óå6WGF–æw4vWD–çFVvW"„Â%v†—FR"ÂgF&vWEv†—FTÆWfVÂ“°Ð¢ÒVÇ6R–b‡5$ò’°Ð¢–çB&ævRÒ°Ð¢5$òÓävWD–çB‚'7W÷'FVDÆWfVÇ2"Âg&ævR“°Ð¢–b‡&ævRÓÒ2’°Ð¢F&vWD&Æ6´ÆWfVÂÒc°Ð¢F&vWEv†—FTÆWfVÂÒ#3S°Ð¢ÐÐ¢ÐÐ Ð¢–b†Õ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÓå6WE6÷W&6UF&vWD–æfò‡—WdÖG&—‚ÂF&vWD&Æ6´ÆWfVÂÂF&vWEv†—FTÆWfVÂ“°Ð¢ÐÐ¢–b†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒ’°Ð¢Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒÓå6WE6÷W&6UF&vWD–æfò‡—WdÖG&—‚ÂF&vWD&Æ6´ÆWfVÂÂF&vWEv†—FTÆWfVÂ“°Ð¢ÐÐ¢Æö6Äg&VR‡—WdÖG&—‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WE7V'F—FÆR†6öç7B7V'F—FÆT–çWBb7V$–çWBÂ&ööÂ6¶—öÆ6–Bò¢ÒfÇ6R¢òÐ§°Ð¢E$4R…õB‚$4Ö–äg&ÖS£¥6WE7V'F—FÆUÆâ"’“°Ð Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢&W6WE7V'F—FÆU÷4æE6—¦R†fÇ6R“°Ð Ð¢&W6WDWFô6÷•7V'F—FÆR‚“°Ð Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð Ð¢&ööÂf—'7GW6RÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÓ°Ð Ð¢–b‡7V$–çWBç7V%7G&VÒ’°Ð¢&ööÂf÷VæBÒfÇ6S°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2’ç7V%7G&VÒ’°Ð¢f÷VæBÒG'VS°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢òòvR&RG'––ærFò6WB7V'F—FÆW27G&VÒF†B—6âwB–âF†RÆ—7B6òvR&÷'B†W&RàÐ¢–b‚f÷VæB’°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ Ð¢–b†Õ÷4bbÕ÷7W'&VçE7V$–çWBç7V%7G&VÒbbÕ÷7W'&VçE7V$–çWBç7V%7G&VÒÒ7V$–çWBç7V%7G&VÒ’°Ð¢Õ÷4Óå6WE7V%–5&÷f–FW"†çVÆÇG"“°Ð¢ÐÐ Ð¢Õ÷7W'&VçE7V$–çWBÒ7V$–çWC°Ð Ð¢–b†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒbbÕ÷6V6öæF'•7V$–çWBç7V%7G&VÒÓÒ7V$–çWBç7V%7G&VÒ’°Ð¢òòF†RæWr&–Ö'’—2F†R7W'&VçB6V6öæF'“²G&÷F†R6V6öæF'’Fòfö–B&VæFW&–ærF†R6ÖRG&6²Gv–6PÐ¢Õ÷6V6öæF'•7V$–çWBÒ7V'F—FÆT–çWB†çVÆÇG"“°Ð¢ÐÐ Ð¢WFFU7V'F—FÆT6öÆ÷$–æfò‚“°Ð¢WFFU7V'F—FÆU&VæFW&–æu&ÖWFW'2‚“°Ð Ð¢–b‚6¶—öÆ6–B’°Ð¢Ä4”BÆ6–BÒ°Ð¢–b†Õ÷7W'&VçE7V$–çWBç7V%7G&VÒbb2ædVæ&ÆU7V'F—FÆW2’°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÓävWE7G&VÔ–æfòƒÂgæÖRÂfÆ6–B“°Ð¢ÐÐ¢–b†Æ6–B’°Ð¢vWDÆö6ÆU7G&–ær†Æ6–BÂÄô4ÄUõ4•4óc3”ÄätäÔS"Â7W'&VçE7V$Æær“°Ð¢ÒVÇ6R°Ð¢7W'&VçE7V$ÆæräV×G’‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b†Õ÷4’°Ð¢uö$W‡FW&æÅ7V'F—FÆRÒ‡7FC£¦f–æB†ÕôW‡FW&æÅ7V'7G&V×2æ6&Vv–â‚’ÂÕôW‡FW&æÅ7V'7G&V×2æ6VæB‚’Â7V$–çWBç7V%7G&VÒ’ÒÕôW‡FW&æÅ7V'7G&V×2æ6VæB‚’“°Ð¢&ööÂW6U÷7V'&W7–æ2ÒfÇ6S°Ð¢–b†WFò%E2ÒG–æÖ–5ö67CÄ5&VæFW&VEFW‡E7V'F—FÆR£â‚„•7V%7G&VÒ¢–Õ÷7W'&VçE7V$–çWBç7V%7G&VÒ’’°Ð¢6–bU4UôÄ”$50Ð¢–b‚%E2ÓæÕôÆ–&746öçFW‡Bä—4Æ–&747F—fR‚’Ð¢6VæF–`Ð¢W6U÷7V'&W7–æ2ÒG'VS°Ð¢ÐÐ¢–b‡W6U÷7V'&W7–æ2’°Ð¢Õ÷væE7V'&W7–æ4&"å6WE7V'F—FÆR‡7V$–çWBç7V%7G&VÒÂÕ÷4ÓävWDe2‚’Âuö$W‡FW&æÅ7V'F—FÆR“°Ð¢ÒVÇ6R°Ð¢Õ÷væE7V'&W7–æ4&"å6WE7V'F—FÆR†çVÆÇG"ÂÕ÷4ÓävWDe2‚’Âuö$W‡FW&æÅ7V'F—FÆR“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†Õ÷4bb2ædVæ&ÆU7V'F—FÆW2’°Ð¢Õ÷4Óå6WE7V%–5&÷f–FW"„vWE7V'F—FÆU7V%–5&÷f–FW"‚’“°Ð¢ÐÐ Ð¢–b‡2æd¶VW†—7F÷'’bb2æ%&VÖVÖ&W%G&6µ6VÆV7F–öâ’°Ð¢2äÕ%RåWFFT7W'&VçE7V'F—FÆUG&6²„vWE6VÆV7FVE7V'F—FÆUG&6´–æFW‚‚’“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WE6V6öæF'•7V'F—FÆR†6öç7B7V'F—FÆT–çWBb7V$–çWBÐ§°Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð Ð¢òòF†RÖVçRÇ&VG’f–ÇFW'2Â'WBwV&BF†R6–æ²2vVÆÂàÐ¢–b‡7V$–çWBç7V%7G&VÒbb—4VÆ–v–&ÆU6V6öæF'•7V'F—FÆR‡7V$–çWB’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢Õ÷6V6öæF'•7V$–çWBÒ7V$–çWC°Ð Ð¢WFFU7V'F—FÆT6öÆ÷$–æfò‚“°Ð¢WFFU7V'F—FÆU&VæFW&–æu&ÖWFW'2‚“°Ð¢ÐÐ Ð¢–b†Õ÷4bbg„vWD6WGF–æw2‚’ædVæ&ÆU7V'F—FÆW2’°Ð¢Õ÷4Óå6WE7V%–5&÷f–FW"„vWE7V'F—FÆU7V%–5&÷f–FW"‚’“°Ð¢ÐÐ§ÐÐ Ð¤46öÕG#Ä•7V%–5&÷f–FW#â4Ö–äg&ÖS£¤vWE7V'F—FÆU7V%–5&÷f–FW"‚Ð§°Ð¢òòF†R&÷f–FW"f÷"F†R7W'&VçB7V'F—FÆR6VÆV7F–öã¢æ÷&ÖÆÇ’F†R&–Ö'Ð¢òò7V'F—FÆR7G&VÒ—G6VÆbÂ'WBv†Vâ6V6öæF'’7V'F—FÆRG&6²—27F—fR&÷F€Ð¢òò7G&V×2&Rw&VB–âÖW&v–ær&÷f–FW"F†B6ö×÷6—FW2F†VÒ–çFòF†PÐ¢òò6ÖR7V'–72Â6òWfW'’&VæFW&W"v÷&·2Væ6†ævVBàÐ¢46öÕG#Ä•7V%–5&÷f–FW#â7V%–5&÷f–FW"„46öÕ•G#Ä•7V%–5&÷f–FW#â†Õ÷7W'&VçE7V$–çWBç7V%7G&VÒ’“°Ð¢46öÕ•G#Ä•7V%–5&÷f–FW#â6V6öæF'•7V%–5&÷f–FW"†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒ“°Ð¢–b‡7V%–5&÷f–FW"bb6V6öæF'•7V%–5&÷f–FW"’°Ð¢7V%–5&÷f–FW"ÒDT%TuôäUr4GVÅ7V%–5&÷f–FW"‡7V%–5&÷f–FW"Â6V6öæF'•7V%–5&÷f–FW"“°Ð¢ÒVÇ6R–b‡6V6öæF'•7V%–5&÷f–FW"’°Ð¢7V%–5&÷f–FW"Ò6V6öæF'•7V%–5&÷f–FW#°Ð¢ÐÐ¢&WGW&â7V%–5&÷f–FW#°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öäVF–õ6†–gDöäöfb‚Ð§°Ð¢g„vWD6WGF–æw2‚’ædVF–õF–ÖU6†–gBÒg„vWD6WGF–æw2‚’ædVF–õF–ÖU6†–gC°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥FövvÆU7V'F—FÆTöäöfb†&ööÂ$F—7Æ”ÖW76vRò£ÒfÇ6R¢òÐ§°Ð¢–b†Õ÷Ee2’°Ð¢&ööÂ$†–FU7V'F—FÆW2ÒfÇ6S°Ð¢Õ÷Ee2ÓævWEô†–FU7V'F—FÆW2‚f$†–FU7V'F—FÆW2“°Ð¢$†–FU7V'F—FÆW2Ò$†–FU7V'F—FÆW3°Ð¢Õ÷Ee2ÓçWEô†–FU7V'F—FÆW2†$†–FU7V'F—FÆW2“°Ð¢ÐÐ¢–b†Õ÷4bb‚Õ÷Ee2ÇÂÕ÷7V%7G&V×2ä—4V×G’‚’’’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢2ædVæ&ÆU7V'F—FÆW2Ò2ædVæ&ÆU7V'F—FÆW3°Ð Ð¢–b‡2ædVæ&ÆU7V'F—FÆW2’°Ð¢6WE7V'F—FÆRƒÂG'VRÂ$F—7Æ”ÖW76vR“°Ð¢ÒVÇ6R°Ð¢–b†Õ÷4’°Ð¢Õ÷4Óå6WE7V%–5&÷f–FW"†çVÆÇG"“°Ð¢ÐÐ¢7W'&VçE7V$ÆærÒ&W57G"„”E5ôuôD•4$ÄTB“°Ð Ð¢–b†$F—7Æ”ÖW76vR’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂ&W57G"„”E5õ5T%D•DÄUõ5E$TÕôôdb’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&WÆ6U7V'F—FÆR†6öç7B•7V%7G&VÒ¢7V%7G&VÔöÆBÂ•7V%7G&VÒ¢7V%7G&VÔæWrÐ§°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢õ4•D”ôâ7W"Ò÷3°Ð¢–b‡7V%7G&VÔöÆBÓÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2’ç7V%7G&VÒ’°Ð¢Õ÷7V%7G&V×2ävWDB†7W"’ç7V%7G&VÒÒ7V%7G&VÔæWs°Ð¢–b†Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÓÒ7V%7G&VÔöÆB’°Ð¢6WE7V'F—FÆR†Õ÷7V%7G&V×2ävWDB†7W"’ÂG'VR“°Ð¢ÒVÇ6R–b†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒÓÒ7V%7G&VÔöÆB’°Ð¢6WE6V6öæF'•7V'F—FÆR†Õ÷7V%7G&V×2ävWDB†7W"’“°Ð¢ÐÐ¢'&V³°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤–çfÆ–FFU7V'F—FÆR„Etõ$EõE"å7V'F—FÆT–Bò£ÒEtõ$EõE%ôÔ‚¢òÂ$TdU$Tä4UõD”ÔR'D–çfÆ–FFRò£ÒÓ¢òÐ§°Ð¢–b†Õ÷4’°Ð¢–b†å7V'F—FÆT–BÓÒEtõ$EõE%ôÔ€Ð¢ÇÂå7V'F—FÆT–BÓÒ„Etõ$EõE"’„•7V%7G&VÒ¢–Õ÷7W'&VçE7V$–çWBç7V%7G&VÐÐ¢ÇÂ†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒbbå7V'F—FÆT–BÓÒ„Etõ$EõE"’„•7V%7G&VÒ¢–Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒ’’°Ð¢Õ÷4Óä–çfÆ–FFR‡'D–çfÆ–FFR“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&VÆöE7V'F—FÆR‚Ð§°Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢Õ÷7V%7G&V×2ävWDæW‡B‡÷2’ç7V%7G&VÒÓå&VÆöB‚“°Ð¢ÐÐ¢ÐÐ Ð¢&W6WE7V'F—FÆU÷4æE6—¦R†fÇ6R“°Ð Ð¢6WE7V'F—FÆRƒÂG'VR“°Ð¢Õ÷væE7V'&W7–æ4&"å&VÆöE7V'F—FÆR‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WE7V'F—FÆUG&6´–G‚†–çB–æFW‚Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbbÕ÷4’°Ð¢òò6†V6²–bvRvçBFò6†ævRF†RVæ&ÆRöF—6&ÆR7FFPÐ¢–b‡2ædVæ&ÆU7V'F—FÆW2Ò†–æFW‚ãÒ’’°Ð¢FövvÆU7V'F—FÆTöäöfb‚“°Ð¢ÐÐ¢òò6WBF†RæWr7V'F—FÆW2G&6²–bæVVFV@Ð¢–b‡2ædVæ&ÆU7V'F—FÆW2’°Ð¢6WE7V'F—FÆR†–æFW‚“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WDVF–õG&6´–G‚†–çB–æFW‚Ð§°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢Etõ$B57G&V×2Ò°Ð¢Etõ$BGtfÆw2ÒÕ5E$TÕ4TÄT5DTä$ÄUôTä$ÄS°Ð¢–b†Õ÷VF–õ7v—F6†W%52bb5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä6÷VçB‚f57G&V×2’’’°Ð¢–b‚†–æFW‚ãÒ’bb†–æFW‚Â‚†–çB–57G&V×2’’’°Ð¢Õ÷VF–õ7v—F6†W%52ÓäVæ&ÆR†–æFW‚ÂGtfÆw2“°Ð Ð¢ÕöÆöFVDVF–õG&6´–æFW‚Ò–æFWƒ°Ð¢Ä4”BÆ6–BÒ°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð¢–b…5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä–æfò†–æFW‚Âg×BÂfGtfÆw2ÂfÆ6–BÂçVÆÇG"Âg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂvWE7G&VÔõ4E7G&–ær„57G&–ær‡7¤æÖR’ÂÆ6–BÂ’“°Ð¢WFFU6VÆV7FVDVF–õ7G&VÔ–æfò†–æFW‚Â×BÂÆ6–B“°Ð¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢òòFôFó¢W6RÕ÷7Æ—GFW%50Ð¢ÐÐ§ÐÐ Ð¦–çB4Ö–äg&ÖS£¤vWD7W'&VçDVF–õG&6´–G‚„57G&–ær§7G$æÖRÐ§°Ð¢–b‡7G$æÖRÐ¢7G$æÖRÓäV×G’‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbbvWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRbbÕ÷t"’°Ð¢Etõ$B57G&V×2Ò°Ð¢–b†Õ÷VF–õ7v—F6†W%52bb5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä6÷VçB‚f57G&V×2’’’°Ð¢f÷"†–çB’Ò²’Â†–çB–57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2Ò°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢–b…5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂçVÆÇG"ÂgæÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢–b†GtfÆw2bÕ5E$TÕ4TÄT5D”ädõôTä$ÄTB’°Ð¢–b‡7G$æÖRÐ¢§7G$æÖRÒæÖS°Ð¢54U%B†ÕöÆöFVDVF–õG&6´–æFW‚ÓÒ’“°Ð¢&WGW&â“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢òòFôFó¢W6RÕ÷7Æ—GFW%50Ð¢ÐÐ¢&WGW&âÓ°Ð§ÐÐ Ð¦–çB4Ö–äg&ÖS£¤vWD7W'&VçE7V'F—FÆUG&6´–G‚„57G&–ær§7G$æÖRÐ§°Ð¢–b‡7G$æÖRÐ¢7G$æÖRÓäV×G’‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’°Ð¢&WGW&âÓ°Ð¢ÐÐ Ð¢–b†Õ÷4bbÕ÷7V%7G&V×2ä—4V×G’‚’’°Ð¢–çB–G‚Ò°Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷2’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBç6÷W&6Tf–ÇFW"’°Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB‡54bÓä6÷VçB‚f57G&V×2’’’°Ð¢6öçF–çVS°Ð¢ÐÐ¢f÷"†–çB¢ÒÂ6çBÒ†–çB–57G&V×3²¢Â6çC²¢²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢–b„d”ÄTB‡54bÓä–æfò†¢ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂgæÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢6öçF–çVS°Ð¢ÐÐ¢–b†Gtw&÷WÒ"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢–b‡7G$æÖRÐ¢§7G$æÖRÒæÖS°Ð¢&WGW&â–Gƒ°Ð¢ÐÐ¢ÐÐ¢–G‚²³°Ð¢ÐÐ¢ÒVÇ6R°Ð¢46öÕG#Ä•7V%7G&VÓâ7V%7G&VÒÒ7V$–çWBç7V%7G&VÓ°Ð¢–b‚7V%7G&VÒ’°Ð¢6öçF–çVS°Ð¢ÐÐ¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢–b‡7G$æÖR’°Ð¢46öÔ†VG#Åt4„#âæÖS°Ð¢7V%7G&VÒÓävWE7G&VÔ–æfò‡7V%7G&VÒÓävWE7G&VÒ‚’ÂgæÖRÂçVÆÇG"“°Ð¢§7G$æÖRÒæÖS°Ð¢ÐÐ¢&WGW&â–G‚²7V%7G&VÒÓävWE7G&VÒ‚“°Ð¢ÐÐ¢–G‚³Ò7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R–b†Õ÷7Æ—GFW%52’°Ð¢Etõ$B57G&V×3°Ð¢–b…5T44TTDTB†Õ÷7Æ—GFW%52Óä6÷VçB‚f57G&V×2’’’°Ð¢–çB–G‚Ò°Ð¢f÷"†–çB’Ò²’Â†–çB–57G&V×3²’²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢46öÔ†VG#Åt4„#â7¤æÖS°Ð Ð¢–b„d”ÄTB†Õ÷7Æ—GFW%52Óä–æfò†’ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’’Ð¢6öçF–çVS°Ð Ð¢–b†Gtw&÷WÒ"Ð¢6öçF–çVS°Ð Ð¢–b†GtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢–b‡7G$æÖRÐ¢§7G$æÖRÒ7¤æÖS°Ð¢&WGW&â–Gƒ°Ð¢ÐÐ Ð¢–G‚²³°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&âÓ°Ð§ÐÐ Ð¥$TdU$Tä4UõD”ÔR4Ö–äg&ÖS£¤vWE÷2‚’6öç7@Ð§°Ð¢&WGW&â„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBòÕ÷væE6VV´&"ävWE÷2‚’¢“°Ð§ÐÐ Ð¥$TdU$Tä4UõD”ÔR4Ö–äg&ÖS£¤vWDGW"‚’6öç7@Ð§°Ð¢õö–çCcB7F'BÂ7F÷°Ð¢Õ÷væE6VV´&"ävWE&ævR‡7F'BÂ7F÷“°Ð¢&WGW&â„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBò7F÷¢“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÆöD¶W”g&ÖW2‚Ð§°Ð¢T”åBä´g2Ò°Ð¢Õö¶g2æ6ÆV"‚“°Ð¢–b†Õ÷´d’bb5ôô²ÓÒÕ÷´d’ÓävWD¶W”g&ÖT6÷VçB†ä´g2’bbä´g2â’°Ð¢T”åB²Òä´g3°Ð¢Õö¶g2ç&W6—¦R†²“°Ð¢–b„d”ÄTB†Õ÷´d’ÓävWD¶W”g&ÖW2‚eD”ÔUôdõ$ÔEôÔTD”õD”ÔRÂÕö¶g2æFF‚’Â²’’ÇÂ²Òä´g2’°Ð¢Õö¶g2æ6ÆV"‚“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤vWD¶W”g&ÖR…$TdU$Tä4UõD”ÔR'EF&vWBÂ$TdU$Tä4UõD”ÔR'DÖ–âÂ$TdU$Tä4UõD”ÔR'DÖ‚Â&ööÂæV&W7BÂ$TdU$Tä4UõD”ÔRb¶W–g&ÖWF–ÖR’6öç7@Ð§°Ð¢54U%B‡'EF&vWBãÒ'DÖ–â“°Ð¢54U%B‡'EF&vWBÃÒ'DÖ‚“°Ð¢–b‚Õö¶g2æV×G’‚’’°Ð¢6öç7BWFò6&Vv–âÒÕö¶g2æ6&Vv–â‚“°Ð¢6öç7BWFò6VæBÒÕö¶g2æ6VæB‚“°Ð¢54U%B‡7FC£¦—5÷6÷'FVB†6&Vv–âÂ6VæB’“°Ð Ð¢WFòf÷VæF¶W–g&ÖRÒ7FC£¦Æ÷vW%ö&÷VæB†6&Vv–âÂ6VæBÂ'EF&vWB“°Ð Ð¢–b†f÷VæF¶W–g&ÖRÓÒ6&Vv–â’°Ð¢òòf—'7B¶W–g&ÖPÐ¢¶W–g&ÖWF–ÖRÒ¦f÷VæF¶W–g&ÖS°Ð¢–b‚†¶W–g&ÖWF–ÖRÂ'DÖ–â’ÇÂ†¶W–g&ÖWF–ÖRâ'DÖ‚’’°Ð¢¶W–g&ÖWF–ÖRÒ'EF&vWC°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R–b†f÷VæF¶W–g&ÖRÓÒ6VæB’°Ð¢òòÆ7B¶W–g&ÖPÐ¢¶W–g&ÖWF–ÖRÒ¢‚ÒÖf÷VæF¶W–g&ÖR“°Ð¢–b†¶W–g&ÖWF–ÖRÂ'DÖ–â’°Ð¢¶W–g&ÖWF–ÖRÒ'EF&vWC°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢¶W–g&ÖWF–ÖRÒ¦f÷VæF¶W–g&ÖS°Ð¢–b†¶W–g&ÖWF–ÖRÓÒ'EF&vWB’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢–b†¶W–g&ÖWF–ÖRâ'DÖ‚’°Ð¢òòW6R&V6VF–ær¶W–g&ÖPÐ¢¶W–g&ÖWF–ÖRÒ¢‚ÒÖf÷VæF¶W–g&ÖR“°Ð¢–b†¶W–g&ÖWF–ÖRÂ'DÖ–â’°Ð¢¶W–g&ÖWF–ÖRÒ'EF&vWC°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†æV&W7B’°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b‡2æTf7E6VV´ÖWF†öBÓÒ2äd5E4TTµôäT$U5Eô´U”e$ÔR’°Ð¢òòW6R6Æ÷6W7B¶W–g&ÖPÐ¢$TdU$Tä4UõD”ÔR&Weö¶W–g&ÖWF–ÖRÒ¢‚ÒÖf÷VæF¶W–g&ÖR“°Ð¢–b‚‡&Weö¶W–g&ÖWF–ÖRãÒ'DÖ–â’’°Ð¢–b‚†¶W–g&ÖWF–ÖRÒ'EF&vWB’â‡'EF&vWBÒ&Weö¶W–g&ÖWF–ÖR’’°Ð¢¶W–g&ÖWF–ÖRÒ&Weö¶W–g&ÖWF–ÖS°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢&WGW&âG'VS°Ð¢ÒVÇ6R°Ð¢¶W–g&ÖWF–ÖRÒ'EF&vWC°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð¥$TdU$Tä4UõD”ÔR4Ö–äg&ÖS£¤vWD6Æ÷6W7D¶W”g&ÖR…$TdU$Tä4UõD”ÔR'EF&vWBÂ$TdU$Tä4UõD”ÔR'DÖ„f÷'v&DF–fbÂ$TdU$Tä4UõD”ÔR'DÖ„&6·v&DF–fb’6öç7@Ð§°Ð¢–b‡'EF&vWBÂÄÂ’&WGW&âÄÃ°Ð¢–b‡'EF&vWBâvWDGW"‚’’&WGW&â'EF&vWC°Ð Ð¢$TdU$Tä4UõD”ÔR'D¶W–g&ÖS°Ð¢$TdU$Tä4UõD”ÔR'DÖ–âÒ7FC£¦Ö‚‡'EF&vWBÒ'DÖ„&6·v&DF–fbÂÄÂ“°Ð¢$TdU$Tä4UõD”ÔR'DÖ‚Ò'EF&vWB²'DÖ„f÷'v&DF–fc°Ð Ð¢–b„vWD¶W”g&ÖR‡'EF&vWBÂ'DÖ–âÂ'DÖ‚ÂG'VRÂ'D¶W–g&ÖR’’°Ð¢&WGW&â'D¶W–g&ÖS°Ð¢ÐÐ¢&WGW&â'EF&vWC°Ð§ÐÐ Ð¥$TdU$Tä4UõD”ÔR4Ö–äg&ÖS£¤vWD6Æ÷6W7D¶W”g&ÖU&Wf–Wr…$TdU$Tä4UõD”ÔR'EF&vWB’6öç7@Ð§°Ð¢&WGW&âvWD6Æ÷6W7D¶W”g&ÖR‡'EF&vWBÂ#ÄÂÂ#ÄÂ“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VVµFò…$TdU$Tä4UõD”ÔR'E÷2Â&ööÂ%6†÷tõ4Bò£ÒG'VR¢òÐ§°Ð¢–b†Õ÷Õ2çÓÒçVÆÇG"’°Ð¢54U%B†fÇ6R“°Ð¢&WGW&ã°Ð¢ÐÐ¢54U%B†Æ7E6VV´f–æ—6‚ãÒÆ7E6VVµ7F'B“²òòFôFó¢&VÖ÷fRÆ7E6VVµ7F'Bf&–&ÆR–bæò&Vw&W76–öç26†÷rW Ð¢TÄôätÄôär7W%F–ÖRÒvWEF–6´6÷VçCcB‚“°Ð¢TÄôätÄôärF–6·56–æ6TÆ7E6VV²Ò7W%F–ÖRÒÆ7E6VV´f–æ—6ƒ°Ð¢TÄôätÄôärÖ–æFVÆ’Ò†Æ7E6VV´f–æ—6‚ÒÆ7E6VVµ7F'B’âCTÄÂòTÄÂ¢CTÄÃ°Ð¢òô54U%B‡'E÷2ÒVWVVE6VV²ç'E÷2ÇÂVWVVE6VV²ç6VVµF–ÖRÓÒÇÂ†7W%F–ÖRÂVWVVE6VV²ç6VVµF–ÖR²STÄÂ’“°Ð Ð¢–b‡F–6·56–æ6TÆ7E6VV²ÂÖ–æFVÆ’’°Ð¢òõE$4R…õB‚$FVÆ’6VV³¢VÇRVÇUÆâ"’Â'E÷2ÂF–6·56–æ6TÆ7E6VV²“°Ð¢VWVVE6VV²Ò²'E÷2Â7W%F–ÖRÂ%6†÷tõ4BÓ°Ð¢6WEF–ÖW"…D”ÔU%ôDTÄ”TE4TT²Â…T”åB’†Ö–æFVÆ’¢ã#RÒF–6·56–æ6TÆ7E6VV²’ÂçVÆÇG"“°Ð¢ÒVÇ6R°Ð¢¶–ÆÅF–ÖW$FVÆ–VE6VV²‚“°Ð¢Æ7E6VVµ7F'BÒ7W%F–ÖS°Ð¢Fõ6VVµFò‡'E÷2Â%6†÷tõ4B“°Ð¢Æ7E6VV´f–æ—6‚ÒvWEF–6´6÷VçCcB‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤Fõ6VVµFò…$TdU$Tä4UõD”ÔR'E÷2Â&ööÂ%6†÷tõ4Bò£ÒG'VR¢òÐ§°Ð¢òõE$4R…õB‚$Fõ6VVµFó¢VÇUÆâ"’Â'E÷2“°Ð Ð¢–b†Õ÷Õ2çÓÒçVÆÇG"’°Ð¢54U%B†fÇ6R“°Ð¢&WGW&ã°Ð¢ÐÐ¢ôf–ÇFW%7FFRg2ÒvWDÖVF–7FFR‚“°Ð Ð¢–b‡'E÷2Â’°Ð¢'E÷2Ò°Ð¢ÐÐ Ð¢–b†%&WVBç÷6—F–öäbb'E÷2Â%&WVBç÷6—F–öäÇÂ%&WVBç÷6—F–öä"bb'E÷2â%&WVBç÷6—F–öä"’°Ð¢F—6&ÆT%&WVB‚“°Ð¢ÐÐ Ð¢–b†Õödg&ÖU7FW–æt7F—fR’°Ð¢òò6æ6VÂVæF–ærg&ÖR7FW0Ð¢Õ÷e2Óä6æ6VÅ7FW‚“°Ð¢Õödg&ÖU7FW–æt7F—fRÒfÇ6S°Ð¢–b†Õ÷$’°Ð¢Õ÷$ÓçWEõföÇVÖR†ÕöåföÇVÖT&Vf÷&Tg&ÖU7FW–ær“°Ð¢ÐÐ¢ÐÐ¢Õöå7FWf÷'v&D6÷VçBÒ°Ð¢&W6WDWFô6÷•7V'F—FÆR‚“°Ð Ð¢òò6¶—6VV·2v†VâGW&F–öâ—2Væ¶æ÷vàÐ¢–b‚Õ÷væE6VV´&"ä†4GW&F–öâ‚’bb‡'E÷2âÄÂÇÂÕ÷væE7FGW4&"ävWEF–ÖW$7W%÷2‚’ÓÒÄÂ’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b‚—5Æ–&6´6GW&TÖöFR‚’’°Ð¢&ööÂf÷&6Uö6ö×ÆWFRÒfÇ6S°Ð¢õö–çCcB7F'BÂ7F÷°Ð¢Õ÷væE6VV´&"ävWE&ævR‡7F'BÂ7F÷“°Ð¢–b‡'E÷2â7F÷’°Ð¢$TdU$Tä4UõD”ÔR'D7W"ÒÕ÷væE6VV´&"ävWE÷2‚“°Ð¢–b‡'D7W"²SÄÂÂ7F÷’°Ð¢òò6¶—Fò÷6—F–öâ6V2&Vf÷&RF†RVæ@Ð¢'E÷2Ò7F÷ÒÄÃ°Ð¢ÒVÇ6R°Ð¢'E÷2Ò7F÷°Ð¢òò6VV¶–ær&W–öæBVæBFöW2æ÷BÇv—2G&–vvW"T5ô4ôÕÄUDPÐ¢f÷&6Uö6ö×ÆWFRÒ‡'D7W"ÓÒ7F÷“°Ð¢ÐÐ¢ÐÐ¢Õ÷væE7FGW4&"å6WE7FGW5F–ÖW"‡'E÷2Â7F÷Â—57V'&W7–æ4&%f—6–&ÆR‚’ÂvWEF–ÖTf÷&ÖB‚’“°Ð Ð¢–b†%6†÷tõ4B’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂÕ÷væE7FGW4&"ävWE7FGW5F–ÖW"‚’ÂS“°Ð¢ÐÐ¢–b†f÷&6Uö6ö×ÆWFR’°Ð¢w&„WfVçD6ö×ÆWFR‚“°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢òõ6ÆVWW‚ƒSÂfÇ6R“²òò'F–f–6–Â6Æ÷r6VV²f÷"FW7F–ærW'÷6W0Ð¢–b„d”ÄTB†Õ÷Õ2Óå6WE÷6—F–öç2‚g'E÷2ÂÕõ4TT´”äuô'6öÇWFU÷6—F–öæ–ærÂçVÆÇG"ÂÕõ4TT´”äuôæõ÷6—F–öæ–ær’’’°Ð¢E$4R…õB‚$”ÖVF–6VV¶–ær6WE÷6—F–öç2f–ÇW&UÆâ"’“°Ð¢–b†%&WVBç÷6—F–öäbb'E÷2ÓÒ%&WVBç÷6—F–öä’°Ð¢F—6&ÆT%&WVB‚“°Ð¢ÐÐ¢ÐÐ¢WFFT6†FW$–ä–æfô&"‚“°Ð¢–b†g2ÓÒ7FFUõ7F÷VB’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBbbÕö”EdDFöÖ–âÓÒEdEôDôÔ”åõF—FÆR’°Ð¢–b†g2ÓÒ7FFUõ7F÷VB’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢g2Ò7FFUõW6VC°Ð¢ÐÐ Ð¢6öç7B$TeD”ÔR&VdfuF–ÖUW$g&ÖRÒvWDfuF–ÖUW$g&ÖR‚“°Ð¢–b†g2ÓÒ7FFUõW6VB’°Ð¢òò§V×öæRÖ÷&Rg&ÖR&6²ÂF†—2—2æVVFVB&V6W6RvRFöâwB†fRç’÷F†W Ð¢òòv’Fò6VV²Fò7V6–f–2F–ÖRv—F†÷WB'Vææ–ærÆ–&6²Fò&Vg&W6‚7FFRàÐ¢'E÷2ÓÒ7FC£¦ÆÇ&÷VæB‡&VdfuF–ÖUW$g&ÖR¢“cB“°Ð¢Õ÷e2Óä6æ6VÅ7FW‚“°Ð¢ÐÐ Ð¢EdEô„Õ4eõD”ÔT4ôDRF2Ò%C$„Õ4b‡'E÷2Âƒãò&VdfuF–ÖUW$g&ÖR’“°Ð¢Õ÷EdD2ÓåÆ”EF–ÖR‚gF2ÂEdEô4ÔEôdÄuô&Æö6²ÂEdEô4ÔEôdÄuôfÇW6‚ÂçVÆÇG"“°Ð Ð¢–b†g2ÓÒ7FFUõW6VB’°Ð¢òòFòg&ÖR7FWFòWFFR7W'&VçB÷6—F–öâ–âW6VB7FFPÐ¢Õ÷e2Óå7FWƒÂçVÆÇG"“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢54U%B„dÅ4R“°Ð¢ÐÐ¢ÕödVæDöe7G&VÒÒfÇ6S°Ð Ð¢öåF–ÖW"…D”ÔU%õ5E$TÕõ5ôÄÄU"“°Ð¢öåF–ÖW"…D”ÔU%õ5E$TÕõ5ôÄÄU#"“°Ð Ð¢–b†g2ÓÒ7FFUõ'Vææ–ærÇÂg2ÓÒ7FFUõW6VB’°Ð¢òòWFFRÖVF–G&ç7÷'B6öçG&öÇ2F–ÖVÆ–æRgFW"6VV°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF–ÖVÆ–æR‡G'VR“°Ð¢6–bÕ5õ4ÕD5õd”DTõõD…TÔ$ä”ÀÐ¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF‡VÖ&æ–Â‚“°Ð¢6VæF–`Ð¢ÐÐ Ð¢6VæD7W'&VçE÷6—F–öåFô’‡G'VR“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6ÆVäw&‚‚Ð§°Ð¢–b‚Õ÷t"’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢46öÕ•G#Ä”Ôf–ÇFW$Ö—64fÆw3âÔÔb‡$b“°Ð¢–b‡ÔÔbbb‡ÔÔbÓävWDÖ—64fÆw2‚’dÕôd”ÅDU%ôÔ•45ôdÄu5ô•5õ4õU$4R’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢òò6öÖR6GW&Rf–ÇFW'2f÷&vWBFò6WBÕôd”ÅDU%ôÔ•45ôdÄu5ô•5õ4õU$4PÐ¢òò÷"Fò–×ÆVÖVçBF†R”Ôf–ÇFW$Ö—64fÆw2–çFW&f6PÐ¢–b‡$bÓÒÕ÷f–D6ÇÂ$bÓÒÕ÷VD6’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢òò‡•7V$f–ÇFW"FöW6âwB†fRç’–ç26öææV7FVBv†Vâ—B—2&VF–æpÐ¢òòW‡FW&æÂ7V'F—FÆW0Ð¢–b„vWD4Å4”B‡$b’ÓÒ4Å4”Eõ‡•7V$f–ÇFW"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b„46öÕ•G#Ä”f–ÆU6÷W&6Tf–ÇFW#â‡$b’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–çBä–âÂä÷WBÂä–ä2Âä÷WD3°Ð¢–b„6÷VçE–ç2‡$bÂä–âÂä÷WBÂä–ä2Âä÷WD2’âbb†ä–ä2²ä÷WD2’ÓÒ’°Ð¢E$4R„57G&–æur„Â%&VÖ÷f–æs¢"’²vWDf–ÇFW$æÖR‡$b’²uÆâr“°Ð Ð¢Õ÷t"Óå&VÖ÷fTf–ÇFW"‡$b“°Ð¢TbÓå&W6WB‚“°Ð¢ÐÐ¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð§ÐÐ Ð¢6FVf–æRTD”ô%TddU$ÄTâS Ð Ð§7FF–2fö–B6WDÆFVæ7’„”&6Tf–ÇFW"¢$bÂ–çB6$'VffW"Ð§°Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢–b„46öÕ•G#Ä”Ô'VffW$æVv÷F–F–öãâÔ$âÒ–â’°Ð¢ÄÄô4Dõ%õ$õU%D”U2°Ð¢æ6$Æ–vâÒÓ²òòÓÖVç2æò&VfW&Væ6RàÐ¢æ6$'VffW"Ò6$'VffW#°Ð¢æ6%&Vf—‚ÒÓ°Ð¢æ4'VffW'2ÒÓ°Ð¢Ô$âÓå7VvvW7DÆÆö6F÷%&÷W'F–W2‚f“°Ð¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¤'V–ÆD6GW&R„•–â¢–âÂ”&6Tf–ÇFW"¢$e³5ÒÂ6öç7BuT”BbÖ¦÷'G—RÂÕôÔTD”õE•R¢×BÐ§°Ð¢”&6Tf–ÇFW"¢'VfbÒ$e³Ó°Ð¢”&6Tf–ÇFW"¢Væ2Ò$e³Ó°Ð¢”&6Tf–ÇFW"¢×W‚Ò$e³%Ó°Ð Ð¢–b‚–âÇÂ×W‚’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢57G&–ærW'#°Ð¢…$U5TÅB‡"Ò5ôô³°Ð¢4f–ÇFW$–æfòf“°Ð Ð¢–b„d”ÄTB‡×W‚ÓåVW'”f–ÇFW$–æfò‚ff’’’ÇÂf’çw&‚’°Ð¢Õ÷t"ÓäFDf–ÇFW"‡×W‚ÂÂ$×VÇF—ÆW†W""“°Ð¢ÐÐ Ð¢57G&–æur&Vf—ƒ°Ð¢57G&–ærG—S°Ð¢–b†Ö¦÷'G—RÓÒÔTD”E•Uõf–FVò’°Ð¢&Vf—‚ÒÂ%f–FVò#°Ð¢G—RäÆöE7G&–ær„”E5ô4EU$UôU%$õ%õd”DTò“°Ð¢ÒVÇ6R–b†Ö¦÷'G—RÓÒÔTD”E•UôVF–ò’°Ð¢&Vf—‚ÒÂ$VF–ò#°Ð¢G—RäÆöE7G&–ær„”E5ô4EU$UôU%$õ%ôTD”ò“°Ð¢ÐÐ Ð¢–b‡'Vfb’°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡'VfbÂ&Vf—‚²Â$'VffW""“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ôDEô%TddU"ÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂ'Vfb“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ô4ôääT5Eô%TdbÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢–âÒvWDf—'7E–â‡'VfbÂ”äD•%ôõUEUB“°Ð¢ÐÐ Ð¢–b‡Væ2’°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡Væ2Â&Vf—‚²Â$Væ6öFW""“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ôDEôTä4ôDU"ÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂVæ2“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ô4ôääT5EôTä2ÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢–âÒvWDf—'7E–â‡Væ2Â”äD•%ôõUEUB“°Ð Ð¢–b„46öÕ•G#Ä”Õ7G&VÔ6öæf–sâÕ42Ò–â’°Ð¢–b‡×BÓæÖ¦÷'G—RÓÒÖ¦÷'G—R’°Ð¢‡"ÒÕ42Óå6WDf÷&ÖB‡×B“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ô4ôÕ$U54”ôâÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢ÐÐ Ð¢òö–b‡×W‚Ð¢°Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂ×W‚“°Ð¢–b„d”ÄTB†‡"’’°Ð¢W'"äf÷&ÖB„”E5ô4EU$UôU%$õ%ôÕTÅD•ÄU„U"ÂG—RävWE7G&–ær‚’“°Ð¢ÖW76vT&÷‚†W'"Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&â‡#°Ð¢ÐÐ¢ÐÐ Ð¢6ÆVäw&‚‚“°Ð Ð¢&WGW&â5ôô³°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤'V–ÆEFô6GW&U&Wf–Wu–â€Ð¢”&6Tf–ÇFW"¢f–D6Â•–â¢¢f–D6–âÂ•–â¢¢f–E&We–âÀÐ¢”&6Tf–ÇFW"¢VD6Â•–â¢¢VD6–âÂ•–â¢¢VE&We–âÐ§°Ð¢…$U5TÅB‡#°Ð¢§f–D6–âÒ§f–E&We–âÒçVÆÇG#°Ð¢§VD6–âÒ§VE&We–âÒçVÆÇG#°Ð¢46öÕG#Ä•–ãâEdVE–ã°Ð Ð¢–b‡f–D6’°Ð¢46öÕG#Ä•–ãâ–ã°Ð¢–b‚VD6òòöæÇ’Æöö²f÷"–çFW&ÆVfVB7G&VÒv†VâvRFöâwBW6Rç’÷F†W"VF–ò6GW&R6÷W&6PÐ¢bb5T44TTDTB†Õ÷4t"Óäf–æE–â‡f–D6Â”äD•%ôõUEUBÂe”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uô–çFW&ÆVfVBÂE%TRÂÂg–â’’’°Ð¢46öÕG#Ä”&6Tf–ÇFW#âEe7Æ—GFW#°Ð¢‡"ÒEe7Æ—GFW"ä6ô7&VFT–ç7Fæ6R„4Å4”EôEe7Æ—GFW"“°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡Ee7Æ—GFW"ÂÂ$Eb7Æ—GFW""“°Ð Ð¢‡"ÒÕ÷4t"Óå&VæFW%7G&VÒ†çVÆÇG"ÂdÔTD”E•Uô–çFW&ÆVfVBÂ–âÂçVÆÇG"ÂEe7Æ—GFW"“°Ð Ð¢–âÒçVÆÇG#°Ð¢‡"ÒÕ÷4t"Óäf–æE–â‡Ee7Æ—GFW"Â”äD•%ôõUEUBÂçVÆÇG"ÂdÔTD”E•Uõf–FVòÂE%TRÂÂg–â“°Ð¢‡"ÒÕ÷4t"Óäf–æE–â‡Ee7Æ—GFW"Â”äD•%ôõUEUBÂçVÆÇG"ÂdÔTD”E•UôVF–òÂE%TRÂÂgEdVE–â“°Ð Ð¢46öÕG#Ä”&6Tf–ÇFW#âEdFV3°Ð¢‡"ÒEdFV2ä6ô7&VFT–ç7Fæ6R„4Å4”EôEef–FVô6öFV2“°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡EdFV2ÂÂ$Ebf–FVòFV6öFW""“°Ð Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂEdFV2“°Ð Ð¢–âÒçVÆÇG#°Ð¢‡"ÒÕ÷4t"Óäf–æE–â‡EdFV2Â”äD•%ôõUEUBÂçVÆÇG"ÂdÔTD”E•Uõf–FVòÂE%TRÂÂg–â“°Ð¢ÒVÇ6R–b„d”ÄTB†Õ÷4t"Óäf–æE–â‡f–D6Â”äD•%ôõUEUBÂe”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uõf–FVòÂE%TRÂÂg–â’’’°Ð¢ÖW76vT&÷‚…&W57G"„”E5ô4EU$UôU%$õ%õd”Eô4Eõ”â’Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢46öÕG#Ä”&6Tf–ÇFW#â6Ö'EFVS°Ð¢‡"Ò6Ö'EFVRä6ô7&VFT–ç7Fæ6R„4Å4”Eõ6Ö'EFVR“°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡6Ö'EFVRÂÂ%6Ö'BFVR‡f–FVò’"“°Ð Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂ6Ö'EFVR“°Ð Ð¢‡"Ò6Ö'EFVRÓäf–æE–â„Â%&Wf–Wr"Âf–E&We–â“°Ð¢‡"Ò6Ö'EFVRÓäf–æE–â„Â$6GW&R"Âf–D6–â“°Ð¢ÐÐ Ð¢–b‡VD6ÇÂEdVE–â’°Ð¢46öÕG#Ä•–ãâ–ã°Ð¢–b‡EdVE–â’°Ð¢–âÒEdVE–ã°Ð¢ÒVÇ6R–b„d”ÄTB†Õ÷4t"Óäf–æE–â‡VD6Â”äD•%ôõUEUBÂe”åô4DTtõ%•ô4EU$RÂdÔTD”E•UôVF–òÂE%TRÂÂg–â’’’°Ð¢ÖW76vT&÷‚…&W57G"„”E5ô4EU$UôU%$õ%ôTEô4Eõ”â’Â&W57G"„”E5ô4EU$UôU%$õ"’ÂÔ%ô”4ôäU%$õ"ÂÔ%ôô²“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢46öÕG#Ä”&6Tf–ÇFW#â6Ö'EFVS°Ð¢‡"Ò6Ö'EFVRä6ô7&VFT–ç7Fæ6R„4Å4”Eõ6Ö'EFVR“°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡6Ö'EFVRÂÂ%6Ö'BFVR†VF–ò’"“°Ð Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"‡–âÂ6Ö'EFVR“°Ð Ð¢‡"Ò6Ö'EFVRÓäf–æE–â„Â%&Wf–Wr"ÂVE&We–â“°Ð¢‡"Ò6Ö'EFVRÓäf–æE–â„Â$6GW&R"ÂVD6–â“°Ð¢ÐÐ Ð¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤'V–ÆDw&…f–FVôVF–ò†–çBee&Wf–WrÂ&ööÂed6GW&RÂ–çBd&Wf–WrÂ&ööÂd6GW&RÐ§°Ð¢ôf–ÇFW%7FFRg2ÒvWDÖVF–7FFR‚“°Ð Ð¢–b†g2Ò7FFUõ7F÷VB’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õ5Dõ“°Ð¢ÐÐ Ð¢…$U5TÅB‡#°Ð Ð¢–b†ee&Wf–Wr’°Ð¢Õôõ4Bå7F÷‚“°Ð Ð¢Õ÷Õe%2å&VÆV6R‚“°Ð¢Õ÷Õe$drå&VÆV6R‚“°Ð¢Õ÷Õe%5"å&VÆV6R‚“°Ð¢Õ÷ÕeDòå&VÆV6R‚“°Ð Ð¢Õ÷42å&VÆV6R‚“°Ð¢Õ÷4"å&VÆV6R‚“°Ð¢Õ÷4å&VÆV6R‚“°Ð¢Õ÷dÕ%t2å&VÆV6R‚“°Ð¢Õ÷dÕ$Ô2å&VÆV6R‚“°Ð¢Õ÷dÔ"å&VÆV6R‚“°Ð¢Õ÷ÔedÔ"å&VÆV6R‚“°Ð¢Õ÷Ôeeå&VÆV6R‚“°Ð¢Õ÷ÔedD2å&VÆV6R‚“°Ð¢Õ÷å&VÆV6R‚“°Ð¢ÐÐ Ð¢Õ÷t"ÓäçV¶TF÷vç7G&VÒ†Õ÷f–D6“°Ð¢Õ÷t"ÓäçV¶TF÷vç7G&VÒ†Õ÷VD6“°Ð Ð¢6ÆVäw&‚‚“°Ð Ð¢–b†Õ÷Õe446’°Ð¢‡"ÒÕ÷Õe446Óå6WDf÷&ÖB‚fÕ÷væD6GW&T&"æÕö6FÆræÕö×Gb“°Ð¢ÐÐ¢–b†Õ÷Õe45&Wb’°Ð¢‡"ÒÕ÷Õe45&WbÓå6WDf÷&ÖB‚fÕ÷væD6GW&T&"æÕö6FÆræÕö×Gb“°Ð¢ÐÐ¢–b†Õ÷Ô42’°Ð¢‡"ÒÕ÷Ô42Óå6WDf÷&ÖB‚fÕ÷væD6GW&T&"æÕö6FÆræÕö×F“°Ð¢ÐÐ Ð¢46öÕG#Ä”&6Tf–ÇFW#âf–D'VffW"ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷f–D'VffW#°Ð¢46öÕG#Ä”&6Tf–ÇFW#âVD'VffW"ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷VD'VffW#°Ð¢46öÕG#Ä”&6Tf–ÇFW#âf–DVæ2ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷f–DVæ3°Ð¢46öÕG#Ä”&6Tf–ÇFW#âVDVæ2ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷VDVæ3°Ð¢46öÕG#Ä”&6Tf–ÇFW#â×W‚ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷×Wƒ°Ð¢46öÕG#Ä”&6Tf–ÇFW#âG7BÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷G7C°Ð¢46öÕG#Ä”&6Tf–ÇFW#âVD×W‚ÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷VD×Wƒ°Ð¢46öÕG#Ä”&6Tf–ÇFW#âVDG7BÒÕ÷væD6GW&T&"æÕö6FÆræÕ÷VDG7C°Ð Ð¢&ööÂdf–ÆT÷WGWBÒ‡×W‚bbG7B’ÇÂ‡VD×W‚bbVDG7B“°Ð¢&ööÂd6GW&RÒ†ed6GW&RÇÂd6GW&R“°Ð Ð¢–b†Õ÷VD6’°Ð¢ÕôÔTD”õE•R¢×BÒfÕ÷væD6GW&T&"æÕö6FÆræÕö×F°Ð¢–çB×2Ò†d6GW&Rbbdf–ÆT÷WGWBbbÕ÷væD6GW&T&"æÕö6FÆræÕödVD÷WGWB’òTD”ô%TddU$ÄTâ¢c°Ð¢–b‡×W‚ÒVD×W‚bbd6GW&R’°Ð¢6WDÆFVæ7’†Õ÷VD6ÂÓ“°Ð¢ÒVÇ6R–b‡×BÓç$f÷&ÖB’°Ð¢6WDÆFVæ7’†Õ÷VD6Â‚…tdTdõ$ÔDU‚¢—×BÓç$f÷&ÖB’Óæäft'—FW5W%6V2¢×2ò“°Ð¢ÐÐ¢ÐÐ Ð¢46öÕG#Ä•–ãâf–D6–âÂf–E&We–âÂVD6–âÂVE&We–ã°Ð¢'V–ÆEFô6GW&U&Wf–Wu–â†Õ÷f–D6Âgf–D6–âÂgf–E&We–âÂÕ÷VD6ÂgVD6–âÂgVE&We–â“°Ð Ð¢òö–b†Õ÷f–D6Ð¢°Ð¢&ööÂef–E&WbÒf–E&We–âbbee&Wf–Ws°Ð¢&ööÂef–D6Òf–D6–âbbed6GW&Rbbdf–ÆT÷WGWBbbÕ÷væD6GW&T&"æÕö6FÆræÕöef–D÷WGWC°Ð Ð¢–b†ee&Wf–WrÓÒ"bbef–D6bbf–D6–â’°Ð¢f–E&We–âÒf–D6–ã°Ð¢f–D6–âÒçVÆÇG#°Ð¢ÐÐ Ð¢–b†ef–E&Wb’°Ð¢Õ÷t"Óå&VæFW"‡f–E&We–â“°Ð Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷4’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷4"’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷42’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÕ%t2’ÂdÅ4R“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÕ$Ô2’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷dÔ"’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷ÔedÔ"’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷ÔedD2’ÂE%TR“°Ð¢Õ÷t"Óäf–æD–çFW&f6R„””Eõeô$u2‚fÕ÷Ôee’ÂE%TR“°Ð¢Õ÷ÕeDòÒÕ÷4°Ð¢Õ÷Õe%5"ÒÕ÷4°Ð¢Õ÷Õe%2ÒÕ÷4°Ð¢Õ÷Õe$drÒÕ÷4°Ð Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢Õ÷f–FVõvæBÒfÕ÷væEf–Ws°Ð Ð¢–b†Õ÷ÔedD2’°Ð¢Õ÷ÔedD2Óå6WEf–FVõv–æF÷r†Õ÷f–FVõvæBÓæÕö…væB“°Ð¢ÒVÇ6R–b†Õ÷dÕ%t2’°Ð¢Õ÷dÕ%t2Óå6WEf–FVô6Æ—–æuv–æF÷r†Õ÷f–FVõvæBÓæÕö…væB“°Ð¢ÐÐ Ð¢–b‡2æe6†÷tõ4BÇÂ2æe6†÷tFV'Vt–æfò’²òòf÷&6Rõ4Böâv†VâF†RFV'Vr7v—F6‚—2W6V@Ð¢–b†Õ÷ÕeDò’°Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷ÕeDò“°Ð¢ÒVÇ6R–b†ÕödgVÆÅ67&VVâbbÕödVF–ôöæÇ’bbÕ÷42’²òòÕ5e Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷dÔ"ÂÕ÷ÔedÔ"ÂfÇ6R“°Ð¢ÒVÇ6R–b‚ÕödVF–ôöæÇ’bb—4C4DgVÆÅ67&VVäÖöFR‚’bb†Õ÷dÔ"ÇÂÕ÷ÔedÔ"’’°Ð¢Õôõ4Bå7F'B†Õ÷f–FVõvæBÂÕ÷dÔ"ÂÕ÷ÔedÔ"ÂG'VR“°Ð¢ÒVÇ6R°Ð¢Õôõ4Bå7F'B†Õ÷õ4EvæB“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†ef–D6’°Ð¢”&6Tf–ÇFW"¢$e³5ÒÒ·f–D'VffW"Âf–DVæ2Â×W‡Ó°Ð¢…$U5TÅB‡#"Ò'V–ÆD6GW&R‡f–D6–âÂ$bÂÔTD”E•Uõf–FVòÂfÕ÷væD6GW&T&"æÕö6FÆræÕö×F7b“°Ð¢Tå$TdU$Tä4TEõ$ÔUDU"†‡#"“°Ð¢ÐÐ Ð¢Õ÷ÔDbå&VÆV6R‚“°Ð¢–b†Õ÷4t"bbd”ÄTB†Õ÷4t"Óäf–æD–çFW&f6R‚e”åô4DTtõ%•ô4EU$RÂdÔTD”E•Uõf–FVòÂÕ÷f–D6Â””Eõeô$u2‚fÕ÷ÔDb’’’’°Ð¢E$4R…õB‚%v&æ–æs¢æò”ÔG&÷VDg&ÖW2–çFW&f6Rf÷"f–F66GW&R"’“°Ð¢ÐÐ¢ÐÐ Ð¢òö–b†Õ÷VD6Ð¢°Ð¢&ööÂdVE&WbÒVE&We–âbbd&Wf–Ws°Ð¢&ööÂdVD6ÒVD6–âbbd6GW&Rbbdf–ÆT÷WGWBbbÕ÷væD6GW&T&"æÕö6FÆræÕödVD÷WGWC°Ð Ð¢–b†d&Wf–WrÓÒ"bbdVD6bbVD6–â’°Ð¢VE&We–âÒVD6–ã°Ð¢VD6–âÒçVÆÇG#°Ð¢ÐÐ Ð¢–b†dVE&Wb’°Ð¢Õ÷t"Óå&VæFW"‡VE&We–â“°Ð¢ÐÐ Ð¢–b†dVD6’°Ð¢”&6Tf–ÇFW"¢$e³5ÒÒ·VD'VffW"ÂVDVæ2ÂVD×W‚òVD×W‚¢×W‡Ó°Ð¢…$U5TÅB‡#"Ò'V–ÆD6GW&R‡VD6–âÂ$bÂÔTD”E•UôVF–òÂfÕ÷væD6GW&T&"æÕö6FÆræÕö×F6“°Ð¢Tå$TdU$Tä4TEõ$ÔUDU"†‡#"“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚†Õ÷f–D6ÇÂÕ÷VD6’bbd6GW&Rbbdf–ÆT÷WGWB’°Ð¢–b‡×W‚ÒG7B’°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡G7BÂÂ$f–ÆRw&—FW"bô"“°Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"„vWDf—'7E–â‡×W‚Â”äD•%ôõUEUB’ÂG7B“°Ð¢ÐÐ Ð¢–b„46öÕ•G#Ä”6öæf–tf”×Wƒâ4ÒÒ×W‚’°Ð¢–çBä–âÂä÷WBÂä–ä2Âä÷WD3°Ð¢6÷VçE–ç2‡×W‚Âä–âÂä÷WBÂä–ä2Âä÷WD2“°Ð¢4ÒÓå6WDÖ7FW%7G&VÒ†ä–ä2Ò“°Ð¢ò÷4ÒÓå6WDÖ7FW%7G&VÒ‚Ó“°Ð¢4ÒÓå6WD÷WGWD6ö×F–&–Æ—G”–æFW‚„dÅ4R“°Ð¢ÐÐ Ð¢–b„46öÕ•G#Ä”6öæf–t–çFW&ÆVf–æsâ4’Ò×W‚’°Ð¢òö–b„d”ÄTB‡4’ÓçWEôÖöFR„”åDU$ÄTdUô4EU$R’’Ð¢–b„d”ÄTB‡4’ÓçWEôÖöFR„”åDU$ÄTdUôäôäUô%TddU$TB’’’°Ð¢4’ÓçWEôÖöFR„”åDU$ÄTdUôäôäR“°Ð¢ÐÐ Ð¢$TdU$Tä4UõD”ÔR'D–çFW&ÆVfRÒ“cB¢TD”ô%TddU$ÄTâÂ'E&W&öÆÂÒ²òó“cB£S Ð¢4’ÓçWEô–çFW&ÆVf–ær‚g'D–çFW&ÆVfRÂg'E&W&öÆÂ“°Ð¢ÐÐ Ð¢–b‡×W‚ÒVD×W‚bbVD×W‚ÒVDG7B’°Ð¢‡"ÒÕ÷t"ÓäFDf–ÇFW"‡VDG7BÂÂ$f–ÆRw&—FW""“°Ð¢‡"ÒÕ÷t"Óä6öææV7Df–ÇFW"„vWDf—'7E–â‡VD×W‚Â”äD•%ôõUEUB’ÂVDG7B“°Ð¢ÐÐ¢ÐÐ Ð¢$TdU$Tä4UõD”ÔR7F÷ÒÔ…õD”ÔS°Ð¢–b†Õ÷4t"’°Ð¢‡"ÒÕ÷4t"Óä6öçG&öÅ7G&VÒ‚e”åô4DTtõ%•ô4EU$RÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"Âg7F÷ÂÂ“²òò7F÷–âF†R–æf–æ—FPÐ¢ÐÐ Ð¢6ÆVäw&‚‚“°Ð Ð¢÷Vå6WGWf–FVò‚“°Ð¢÷Vå6WGWVF–ò‚“°Ð¢÷Vå6WGW7FG4&"‚“°Ð¢÷Vå6WGW7FGW4&"‚“°Ð¢&V6Æ4Æ–÷WB‚“°Ð Ð¢6WGWdÕ#”6öÆ÷$6öçG&öÂ‚“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢–b†g2ÓÒ7FFUõ'Vææ–ær’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ’“°Ð¢ÒVÇ6R–b†g2ÓÒ7FFUõW6VB’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥7F'D6GW&R‚Ð§°Ð¢–b‚Õ÷4t"ÇÂÕöd6GW&–ær’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b‚Õ÷væD6GW&T&"æÕö6FÆræÕ÷×W‚bbÕ÷væD6GW&T&"æÕö6FÆræÕ÷G7B’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢…$U5TÅB‡#°Ð Ð¢£¥6WE&–÷&—G”6Æ72ƒ£¤vWD7W'&VçE&ö6W72‚’Â„”t…õ$”õ$•E•ô4Ä52“°Ð Ð¢òò&&RFò6VRGvò6GW&Rf–ÇFW'2Fò7W÷'B”ÕW6…6÷W&6RBF†R6ÖRF–ÖRââàÐ¢òö‡"Ò46öÕ•G#Ä”Ôw&…7G&V×3â†Õ÷t"’Óå7–æ5W6–æu7G&VÔöfg6WB…E%TR“²òòDôDó Ð Ð¢'V–ÆDw&…f–FVôVF–ò€Ð¢Õ÷væD6GW&T&"æÕö6FÆræÕöef–E&Wf–WrÂG'VRÀÐ¢Õ÷væD6GW&T&"æÕö6FÆræÕödVE&Wf–WrÂG'VR“°Ð Ð¢‡"ÒÕ÷ÔRÓä6æ6VÄFVfVÇD†æFÆ–ær„T5õ$U”åB“°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ’“°Ð¢Õöd6GW&–ærÒG'VS°Ð Ð¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥7F÷6GW&R‚Ð§°Ð¢–b‚Õ÷4t"ÇÂÕöd6GW&–ær’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b‚Õ÷væD6GW&T&"æÕö6FÆræÕ÷×W‚bbÕ÷væD6GW&T&"æÕö6FÆræÕ÷G7B’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR…7G%&W2„”E5ô4ôåE$ôÅ5ô4ôÕÄUD”är’“°Ð¢Õöd6GW&–ærÒfÇ6S°Ð Ð¢'V–ÆDw&…f–FVôVF–ò€Ð¢Õ÷væD6GW&T&"æÕö6FÆræÕöef–E&Wf–WrÂfÇ6RÀÐ¢Õ÷væD6GW&T&"æÕö6FÆræÕödVE&Wf–WrÂfÇ6R“°Ð Ð¢Õ÷ÔRÓå&W7F÷&TFVfVÇD†æFÆ–ær„T5õ$U”åB“°Ð Ð¢£¥6WE&–÷&—G”6Æ72ƒ£¤vWD7W'&VçE&ö6W72‚’Âg„vWD6WGF–æw2‚’æGu&–÷&—G’“°Ð Ð¢Õ÷'DGW&F–öä÷fW'&–FRÒÓ°Ð Ð¢&WGW&âG'VS°Ð§ÐÐ Ð¢òðÐ Ð§fö–B4Ö–äg&ÖS£¥6†÷t÷F–öç2†–çB–EvRò¢Ò¢òÐ§°Ð¢òòF—6&ÆRF†R÷F–öç2F–Æörv†VâW6–ærC4BgVÆÇ67&VVàÐ¢–b„—4C4DgVÆÅ67&VVäÖöFR‚’bbÕö$gVÆÅ67&VVåv–æF÷t—4öå6W&FTF—7Æ’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òò6†÷rv&æ–ærv†Vâ”ä’f–ÆR—2&VBÖöæÇÐ¢5F‚–æ•F‚Òg„vWD×”‚’ÓävWD–æ•F‚‚“°Ð¢–b…F…WF–Ç3£¤W†—7G2†–æ•F‚’’°Ð¢„äDÄR„f–ÆRÒ7&VFTf–ÆR†–æ•F‚ÂtTäU$”5õu$•DRÂd”ÄUõ4„$Uõ$TBÂd”ÄUõ4„$Uõu$•DRÂd”ÄUõ4„$UôDTÄUDRÂçVÆÇG"ÂõTåôU„•5D”ärÂd”ÄUôdÄuô$4µUõ4TÔåD”52ÂçVÆÇG"“°Ð¢–b†„f–ÆRÓÒ”ådÄ”Eô„äDÄUõdÅTR’°Ð¢g„ÖW76vT&÷‚…õB‚%F†RÆ–W"6WGF–æw2&R7W'&VçFÇ’7F÷&VB–ââ”ä’f–ÆRÆö6FVB–âF†R–ç7FÆÆF–öâF—&V7F÷'’öbF†RÆ–W"åÆåÆåF†RÆ–W"7W'&VçFÇ’FöW2æ÷B†fRw&—FR66W72FòF†—2f–ÆRÂÖVæ–ærç’6†ævW2FòF†R6WGF–æw2v–ÆÂæ÷B&R6fVBåÆåÆåÆV6R&VÖ÷fRF†R”ä’f–ÆRFòVç7W&R&÷W"gVæ7F–öæÆ—G’öbF†RÆ–W"åÆåÆå6WGF–æw2v–ÆÂF†Vâ&R7F÷&VB–âF†Rv–æF÷w2&Vv—7G'’â–÷R6âV6–Ç’&6·WF†÷6R6WGF–æw2F‡&÷Vvƒ¢÷F–öç2âÖ—66VÆÆæV÷W2âW‡÷'B"’ÂÔ%ô”4ôåt$ä”ärÂ“°Ð¢ÐÐ¢6Æ÷6T†æFÆR†„f–ÆR“°Ð¢ÐÐ Ð¢”åEõE"•&W3°Ð¢Fò°Ð¢5vU6†VWB÷F–öç2…&W57G"„”E5ôõD”ôå5ô4D”ôâ’ÂÕ÷t"ÂvWDÖöFÅ&VçB‚’Â–EvR“°Ð¢•&W2Ò÷F–öç2äFôÖöFÂ‚“°Ð¢–EvRÒ²òò–bvR&RFò6†÷rF†RF–Æörv–âÂÇv—26†÷rF†RÆFW7BvPÐ¢Òv†–ÆR†•&W2ÓÒ5vU6†VWC£¤Å•ôÄäuTtUô4„ätR“²òò6†V6²–bvRW†—FVBF†RF–Æör6òF†BF†RÆæwVvR6†ævR6â&RÆ–V@Ð Ð¢7v—F6‚†•&W2’°Ð¢66R5vU6†VWC£¥$U4UEõ4UED”äu3 Ð¢òò&WVW7BÕ2Ô„2Fò6Æ÷6R—G6VÆ`Ð¢6VæDÖW76vR…tÕô4Äõ4R“°Ð¢òòæB–ÖÖVF–FVÇ’&V÷VàÐ¢6†VÆÄW†V7WFR†çVÆÇG"ÂõB‚&÷Vâ"’ÂF…WF–Ç3£¤vWE&öw&ÕF‚‡G'VR’ÂõB‚"÷&W6WB"’ÂçVÆÇG"Â5uõ4„õtäõ$ÔÂ“°Ð¢'&V³°Ð¢FVfVÇC Ð¢54U%B†•&W2Ò5vU6†VWC£¤Å•ôÄäuTtUô4„ätR“°Ð¢'&V³°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7F'EvV%6W'fW"†–çBå÷'BÐ§°Ð¢–b‚Õ÷vV%6W'fW"’°Ð¢Õ÷vV%6W'fW"äGF6‚„DT%TuôäUr5vV%6W'fW"‡F†—2Âå÷'B’“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7F÷vV%6W'fW"‚Ð§°Ð¢–b†Õ÷vV%6W'fW"’°Ð¢Õ÷vV%6W'fW"äg&VR‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæE7FGW4ÖW76vR„57G&–ær×6rÂ–çBåF–ÖT÷WBÂ&ööÂ%&WfVÅ7FGW4&"ò¢ÒfÇ6R¢òÀÐ¢&ööÂ$¶VWf—6–&ÆTöäÖVF–ÆöBò¢ÒfÇ6R¢òÐ§°Ð¢6öç7BWFòF–ÖW$–BÒF–ÖW$öæUF–ÖU7V'67&–&W#£¥5DEU5ôU$4S°Ð Ð¢Õ÷F–ÖW$öæUF–ÖRåVç7V'67&–&R‡F–ÖW$–B“°Ð Ð¢òòæöâ×&WfVÆ–ær&WÆ6VÖVçB6ææ÷B–æ†W&—Bf÷&6VB×f—6–&ÆR7FGW2&"g&öÒâÐ¢òòÖW76vRv†÷6RF–ÖW"†2§W7B&VVâ6æ6VÆÆVBàÐ¢–b†Õö$¶VWFV×7FGW4&%f—6–&ÆTöäÖVF–ÆöBbb†åF–ÖT÷WBâbb%&WfVÅ7FGW4&"’’°Ð¢&W7F÷&U7FGW4&$ÖW76vT†öÆB‚“°Ð¢ÐÐ¢Õö$¶VWFV×7FGW4&%f—6–&ÆTöäÖVF–ÆöBÒfÇ6S°Ð Ð¢Õ÷FV×7FGW5ö×6räV×G’‚“°Ð¢–b†åF–ÖT÷WBÃÒ’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢Õ÷FV×7FGW5ö×6rÒ×6s°Ð¢Õö$¶VWFV×7FGW4&%f—6–&ÆTöäÖVF–ÆöBÒ%&WfVÅ7FGW4&"bb$¶VWf—6–&ÆTöäÖVF–ÆöC°Ð¢òò6ÆÆW"Ö’'&–VfÇ’&WfVÂ&W6WBÖ†–FFVâ7FGW2&#²&RÖ†–FR—Bv†VâF†PÐ¢òòÖW76vRF–ÖW2÷WB6ò&V7W'&–ærÖW76vW26ææ÷B–â—B÷Vâ‚33#Sb’àÐ¢Õ÷F–ÖW$öæUF–ÖRå7V'67&–&R‡F–ÖW$–BÂ·F†—2Â%&WfVÅ7FGW4&%Ò°Ð¢Õ÷FV×7FGW5ö×6räV×G’‚“°Ð¢Õö$¶VWFV×7FGW4&%f—6–&ÆTöäÖVF–ÆöBÒfÇ6S°Ð¢–b†%&WfVÅ7FGW4&"’°Ð¢&W7F÷&U7FGW4&$ÖW76vT†öÆB‚“°Ð¢ÐÐ¢ÒÂåF–ÖT÷WB“°Ð Ð¢–b‚Õ÷FV×7FGW5ö×6rä—4V×G’‚’’°Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR†Õ÷FV×7FGW5ö×6r“°Ð¢–b†%&WfVÅ7FGW4&"’°Ð¢6†÷u7FGW4&$f÷$ÖW76vR‚“°Ð¢ÐÐ¢ÐÐ Ð¢ÕôÆ6Bå6WE7FGW4ÖW76vR†×6rÂåF–ÖT÷WB“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤6å&Wf–WuW6R‚’°Ð¢&WGW&â†Õö%W6U6VVµ&Wf–WrbbÕ÷væE&Uf–WrbbÕödVF–ôöæÇ’bbÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDT@Ð¢bb„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBÇÂvWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷Vä7W%Æ–Æ—7D—FVÒ…$TdU$Tä4UõD”ÔR'E7F'BÂ&ööÂ&V÷Vâò¢ÒfÇ6R¢òÂ%&WVB%&WVBò¢Ò%&WVB‚’¢òÐ§°Ð¢–b„—5Æ–Æ—7DV×G’‚’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b‚Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’’°Ð¢Õ÷væEÆ–Æ—7D&"å6WDf—'7E6VÆV7FVB‚“°Ð¢–b‚Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ Ð¢–b‡Æ’æÕö%–÷WGV&TDÂbb‡&V÷VâÇÂÆ’æÕöfç2ävWD†VB‚’ÓÒÆ’æÕ÷–FÅ6÷W&6UU$ÂbbÕ÷7–FÄÆ7E&ö6W75U$ÂÒÆ’æÕ÷–FÅ6÷W&6UU$Â’’°Ð¢–b‚6Æ÷6TÖVF–&Vf÷&T÷Vâ‚’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b…&ö6W75–÷WGV&TDÅU$Â‡Æ’æÕ÷–FÅ6÷W&6UU$ÂÂfÇ6RÂG'VR’’°Ð¢÷Vä7W%Æ–Æ—7D—FVÒ‡'E7F'BÂfÇ6R“°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ Ð¢4WFõG#Ä÷VäÖVF–FFâ†Õ÷væEÆ–Æ—7D&"ävWD7W$ôÔB‡'E7F'BÂ%&WVB’“°Ð¢–b‡’°Ð¢÷VäÖVF–‡“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤FD7W$FWeFõÆ–Æ—7B‚Ð§°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôäÄôuô4EU$R’°Ð¢Õ÷væEÆ–Æ—7D&"äVæB€Ð¢Õõf–DF—7æÖRÀÐ¢ÕôVDF—7æÖRÀÐ¢Õ÷væD6GW&T&"æÕö6FÆrävWEf–FVô–çWB‚’ÀÐ¢Õ÷væD6GW&T&"æÕö6FÆrävWEf–FVô6†ææVÂ‚’ÀÐ¢Õ÷væD6GW&T&"æÕö6FÆrävWDVF–ô–çWB‚Ð¢“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤÷VäÖVF–„4WFõG#Ä÷VäÖVF–FFâôÔBÐ§°Ð¢òòæW‡BÖVF–ÆöC¢7F÷f÷&6R×6†÷v–ærF†R7FGW2&"F†BâV&Æ–W"W'&÷"&WfVÆVBâÐ¢òò†÷7B×7WÆ–VB7FGW2ÖW76vR¶VW2—G2÷vâF‡&VR×6V6öæB&WfVÂ7&÷72F†—2G&ç6—F–öâàÐ¢–b‚Õö$¶VWFV×7FGW4&%f—6–&ÆTöäÖVF–ÆöB’°Ð¢&W7F÷&U7FGW4&$ÖW76vT†öÆB‚“°Ð¢ÐÐ Ð¢WFòf–ÆTFFÒG–æÖ–5ö67CÆ6öç7B÷Väf–ÆTFF£â‡ôÔBæÕ÷“°Ð¢òöWFòEdDFFÒG–æÖ–5ö67CÆ6öç7B÷VäEdDFF£â‡ôÔBæÕ÷“°Ð¢WFòFWf–6TFFÒG–æÖ–5ö67CÆ6öç7B÷VäFWf–6TFF£â‡ôÔBæÕ÷“°Ð Ð¢òò–bF†RGVæW"w&‚—2Ç&VG’ÆöFVBÂvR§W7B6†ævR—G26†ææVÀÐ¢–b‡FWf–6TFF’°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbbÕ÷ÕGVæW Ð¢bbÕõf–DF—7æÖRÓÒFWf–6TFFÓäF—7Æ”æÖU³ÒbbÕôVDF—7æÖRÓÒFWf–6TFFÓäF—7Æ”æÖU³Ò’°Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WEf–FVô–çWB‡FWf–6TFFÓçf–çWB“°Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WEf–FVô6†ææVÂ‡FWf–6TFFÓçf6†ææVÂ“°Ð¢Õ÷væD6GW&T&"æÕö6FÆrå6WDVF–ô–çWB‡FWf–6TFFÓæ–çWB“°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b†Õô7F—fTw&„æ÷F–g”Wd6öFRÓÒT5õU4TBÇÂÕôöä6Æ÷6Uö6ÆÆVB’°Ð¢54U%B†fÇ6R“°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢6VæF–`Ð¢ÐÐ Ð¢–b†Õö$÷VäÖVF–7F—fR’°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–‡F‡&VBVÇR’Óâ6¶—–ær&V6W6RF†W&RÇ&VG’—2â7F—fR÷VäÖVF–6ÆÂ"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢E$4R…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–‡F‡&VBVÇR’Óâ6¶—–ær&V6W6RF†W&RÇ&VG’—2â7F—fR÷VäÖVF–6ÆÅÆâ"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢&WGW&ã°Ð¢ÒVÇ6R°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–‡F‡&VBVÇR’"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢E$4R…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–‡F‡&VBVÇR•Æâ"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢ÐÐ¢Õö$÷VäÖVF–7F—fRÒG'VS°Ð Ð¢–b‚6Æ÷6TÖVF–&Vf÷&T÷Vâ‚’’°Ð¢Õö$÷VäÖVF–7F—fRÒfÇ6S°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òò–bF†Rf–ÆR—2öâ6öÖR&VÖ÷f&ÆRG&—fRæBF†BG&—fR—2Ö—76–ærÀÐ¢òòvR–VÆÂBW6W"&Vf÷&RWfVâG'––ærFò6öç7G'V7BF†Rw&€Ð¢–b‡f–ÆTFF’°Ð¢57G&–ærfâÒf–ÆTFFÓæfç2ävWD†VB‚“°Ð¢–çB’Òfâäf–æB…õB‚#¥ÅÂ"’“°Ð¢–b†’â’°Ð¢57G&–ærG&—fRÒfâäÆVgB†’²"“°Ð¢T”åBG—RÒvWDG&—fUG—R†G&—fR“°Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð¢–b‡G—RÓÒE$•dUõ$TÔõd$ÄRÇÂG—RÓÒE$•dUô4E$ôÒbbvWD÷F–6ÄF—6µG—R†G&—fU³ÒÂ6Â’Ò÷F–6ÄF—6µôVF–ò’°Ð¢–çB&WBÒ”E$UE%“°Ð¢v†–ÆR‡&WBÓÒ”E$UE%’’°Ð¢t”ã3%ôd”äEôDDf–æDf–ÆTFF°Ð¢„äDÄR‚Òf–æDf—'7Df–ÆR†fâÂff–æDf–ÆTFF“°Ð¢–b†‚Ò”ådÄ”Eô„äDÄUõdÅTR’°Ð¢f–æD6Æ÷6R†‚“°Ð¢&WBÒ”Dô³°Ð¢ÒVÇ6R°Ð¢57G&–ær×6s°Ð¢×6räf÷&ÖB„”E5ôÔ”äe$ÕóBÂfâävWE7G&–ær‚’“°Ð¢&WBÒg„ÖW76vT&÷‚†×6rÂÔ%õ$UE%”4ä4TÂ“°Ð¢ÐÐ¢ÐÐ¢–b‡&WBÒ”Dô²’°Ð¢Õö$÷VäÖVF–7F—fRÒfÇ6S°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†ÕöTÖVF–ÆöE7FFRÒÔÅ3£¤4Äõ4TB’°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢6VæF–`Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òò6ÆV"$BÆ–Æ—7B–bvR&Ræ÷B7W'&VçFÇ’÷Væ–ær6öÖWF†–ærg&öÒ—@Ð¢–b‚Õö$—4$EÆ’’°Ð¢ÕôÕÅ5Æ–Æ—7Bæ6ÆV"‚“°Ð¢ÕôÆ7D÷Vä$EF‚ÒõB‚""“°Ð¢ÐÐ¢Õö$—4$EÆ’ÒfÇ6S°Ð Ð¢òòæòæVVBFòG'’&VÆV6–ærW‡FW&æÂö&¦V7G2v†–ÆRÆ––æpÐ¢¶–ÆÅF–ÖW"…D”ÔU%õTäÄôEõTåU4TEôU…DU$äÅôô$¤T5E2“°Ð Ð¢òòvR†W&V'’&ö6Æ–ÐÐ¢6WDÆöE7FFR„ÔÅ3£¤ÄôD”är“°Ð Ð¢òòW6RF†Rw&‚F‡&VBöæÇ’f÷"6öÖRÖVF–G—W0Ð¢&ööÂ$F—&V7E6†÷rÒf–ÆTFFbbf–ÆTFFÓæfç2ä—4V×G’‚’bb2æÕôf÷&ÖG2ävWDVæv–æR‡f–ÆTFFÓæfç2ävWD†VB‚’’ÓÒF—&V7E6†÷s°Ð¢&ööÂ%W6UF‡&VBÒÕ÷w&…F‡&VBbb2ædVæ&ÆUv÷&¶W%F‡&VDf÷$÷Væ–ærbb†$F—&V7E6†÷rÇÂf–ÆTFF’bb‡2æ”FVfVÇD6GW&TFWf–6RÓÒÇÂFWf–6TFF“² Ð¢–b†%W6UF‡&VBbb‚Õ÷w&…F‡&VBÓæÕö…F‡&VBÇÂÕ÷w&…F‡&VBÓæ‡%ö6ö–æ—BÒ5ôô²’’°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–Òw&‚F‡&VB–æ—BW'&÷"ƒ‚S…‚’Ò&ö6VVF–ærv—F†÷WBv÷&¶W"F‡&VB"’ÂÕ÷w&…F‡&VBÓæ‡%ö6ö–æ—B“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢%W6UF‡&VBÒfÇ6S°Ð¢Õ÷w&…F‡&VBÒçVÆÇG#°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ Ð¢&ööÂv4Ö†–Ö—¦VBÒ—5¦ööÖVB‚“°Ð¢òò7&VFRC6Fg2v–æF÷r–bÆVæ6†–ær–âgVÆÇ67&VVâæBC6Fg2—2Væ&ÆV@Ð¢–b‡2ä—4C4DgVÆÇ67&VVâ‚’bbÕöe7F'D–äC4DgVÆÇ67&VVâ’°Ð¢7&VFTgVÆÅ67&VVåv–æF÷r‚“°Ð¢Õ÷f–FVõvæBÒÕ÷FVF–6FVDe5f–FVõvæC°Ð¢Õöe7F'D–äC4DgVÆÇ67&VVâÒfÇ6S°Ð¢ÒVÇ6R–b†Õöe7F'D–ägVÆÇ67&VVå6W&FR’°Ð¢7&VFTgVÆÅ67&VVåv–æF÷r†fÇ6R“°Ð¢Õ÷f–FVõvæBÒÕ÷FVF–6FVDe5f–FVõvæC°Ð¢Õöe7F'D–ägVÆÇ67&VVå6W&FRÒfÇ6S°Ð¢Õö$æVVE¦ööÔgFW$gVÆÇ67&VVäW†—BÒG'VS°Ð¢ÒVÇ6R°Ð¢Õ÷f–FVõvæBÒfÕ÷væEf–Ws°Ð¢ÐÐ Ð¢òò7F—fFRWFòÖf—BÆöv–2WöâW†—F–ærgVÆÇ67&VVâ–`Ð¢òòvR&R÷Væ–æræWrÖVF––âgVÆÇ67&VVâÖöFPÐ¢òòF—÷6S¢VæÆW72vRvW&R&Wf–÷W6Ç’Ö†–Ö—¦V@Ð¢–b‚„—4gVÆÅ67&VVäÖöFR‚’’bb2æe&VÖVÖ&W%¦ööÔÆWfVÂbbv4Ö†–Ö—¦VB’°Ð¢Õö$æVVE¦ööÔgFW$gVÆÇ67&VVäW†—BÒG'VS°Ð¢ÐÐ Ð¢òòFöâwB6WBf–FVò&VæFW&W"÷WGWB&V7BVçF–ÂF†Rv–æF÷r—2&W÷6—F–öæV@Ð¢Õö$FVÆ•6WD÷WGWE&V7BÒG'VS°Ð Ð¢6–b Ð¢òòF—7Æ’6÷'&W7öæF–ærÖVF––6öâ–â7FGW2& Ð¢–b‡f–ÆTFF’°Ð¢57G&–ærf–ÆVæÖRÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‚“°Ð¢57G&–ærW‡BÒf–ÆVæÖRäÖ–B†f–ÆVæÖRå&WfW'6Tf–æB‚râr’²“°Ð¢Õ÷væE7FGW4&"å6WDÖVF–G—R†W‡B“°Ð¢ÒVÇ6R–b‡EdDFF’°Ð¢Õ÷væE7FGW4&"å6WDÖVF–G—R…õB‚"æ–fò"’“°Ð¢ÒVÇ6R°Ð¢òòDôDó¢7&VFR–6öç2f÷"FWf–6TFFÐ¢Õ÷væE7FGW4&"å6WDÖVF–G—R…õB‚"çVæ¶æ÷vâ"’“°Ð¢ÐÐ¢6VæF–`Ð Ð¢òò–æ—F–FRw&‚7&VF–öâÂ÷VäÖVF–&—fFR‚’v–ÆÂ6ÆÂöäf–ÆU÷7D÷VæÖVF–‚Ð¢–b†%W6UF‡&VB’°Ð¢÷VäÖVF–FF¢ôÔD6÷’ÒôÔBäFWF6‚‚“°Ð¢–b†ÕöWd÷Vå&—fFTf–æ—6†VBå&W6WB‚’bbÕ÷w&…F‡&VBÓå÷7EF‡&VDÖW76vR„4w&…F‡&VC£¥DÕôõTâÂ…u$Ò“Â„Å$Ò—ôÔD6÷’’’°Ð¢Õö$÷VæVEF‡&÷Vv…F‡&VBÒG'VS°Ð¢ÒVÇ6R°Ð¢–çBÆ7FW'&÷"ÒvWDÆ7DW'&÷"‚“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤÷VäÖVF–Òf–ÆVBFòW6Rw&‚v÷&¶–ærF‡&VB†W'&÷"VB’"’ÂÆ7FW'&÷"“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢%W6UF‡&VBÒfÇ6S°Ð¢Õ÷w&…F‡&VBÒçVÆÇG#°Ð¢ôÔBäGF6‚‡ôÔD6÷’“°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚%W6UF‡&VB’°Ð¢Õö$÷VæVEF‡&÷Vv…F‡&VBÒfÇ6S°Ð¢÷VäÖVF–&—fFR‡ôÔB“°Ð¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥&W6WDFWf–6R‚Ð§°Ð¢–b…U4UôÄôttU"„g„vWD6WGF–æw2‚’’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¥&W6WDFWf–6R"’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢–b†Õ÷4%÷&Wf–Wr’°Ð¢Õ÷4%÷&Wf–WrÓå&W6WDFWf–6R‚“°Ð¢ÐÐ¢–b†Õ÷4’°Ð¢&WGW&âÕ÷4Óå&W6WDFWf–6R‚“°Ð¢ÐÐ¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤F—7Æ”6†ævR‚Ð§°Ð¢–b…U4UôÄôttU"„g„vWD6WGF–æw2‚’’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤F—7Æ”6†ævR"’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢–b†Õ÷4%÷&Wf–Wr’°Ð¢Õ÷4%÷&Wf–WrÓäF—7Æ”6†ævR‚“°Ð¢ÐÐ¢–b†Õ÷4’°Ð¢&WGW&âÕ÷4ÓäF—7Æ”6†ævR‚“°Ð¢ÐÐ¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤6Æ÷6TÖVF–&Vf÷&T÷Vâ‚Ð§°Ð¢–b†ÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDTBÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôD”ärÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤d”Ä”är’°Ð¢6Æ÷6TÖVF–‡G'VR“°Ð¢ÒVÇ6R–b†ÕöTÖVF–ÆöE7FFRÒÔÅ3£¤4Äõ4TB’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–&Vf÷&T÷VâÒVæW‡V7FVBÆöG7FFRVB"’ÂÕöTÖVF–ÆöE7FFR“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢54U%B†fÇ6R“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢–b„g„vWD×”‚’ÓæÕöd6Æ÷6–æu7FFR’°Ð¢54U%B†fÇ6R“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢&WGW&âG'VS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤f÷&6T6Æ÷6U&ö6W72‚Ð§°Ð¢ÖW76vT&VW„Ô%ô”4ôäU„4ÄÔD”ôâ“°Ð¢–b…U4UôÄôttU"„g„vWD6WGF–æw2‚’’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤f÷&6T6Æ÷6U&ö6W72"’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢7&6…&W÷'FW#£¤F—6&ÆR‚“°Ð¢ÐÐ¢FW&Ö–æFU&ö6W72„vWD7W'&VçE&ö6W72‚’Â„DTD$TTb“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6Æ÷6TÖVF–†&ööÂ$æW‡D—5VWVVBò¢ÒfÇ6R¢òÂ&ööÂ%VæF–ætf–ÆTFVÆWFRò¢ÒfÇ6R¢òÐ§°Ð¢E$4R…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–Æâ"’“°Ð Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð Ð¢&ööÂ†–&W&æF–ærÒ†ÕöGtÆ7EW6RÓÒTÄÂ“°Ð¢ÕöGtÆ7EW6RÒTÄÃ°Ð Ð¢–b†Õö%W6U6VVµ&Wf–WrbbÕ÷væE&Uf–Wrä—5v–æF÷uf—6–&ÆR‚’’°Ð¢Õ÷væE&Uf–Wrå6†÷uv–æF÷r…5uô„”DR“°Ð¢ÐÐ¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢Õö$EdE7F–ÆÄöâÒfÇ6S°Ð Ð¢–b†Õô7F—fTw&„æ÷F–g”Wd6öFRÓÒT5õU4TB’°Ð¢54U%B†fÇ6R“°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢6VæF–`Ð¢ÐÐ Ð¢–b†ÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤4Äõ4TB’°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–‡F‡&VBVÇR’Ò–væ÷&–ær&V6W6RÇ&VG’6Æ÷6VB"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢E$4R…õB‚$–væ÷&–ærGWÆ–6FR6Æ÷6R7F–öâåÆâ"’“°Ð¢&WGW&ã°Ð¢ÐÐ¢–b†ÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤4Äõ4”ärÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤$õ%D”är’°Ð¢E$4R…õB‚$GWÆ–6FR6Æ÷6R7F–öâåÆâ"’“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–‡F‡&VBVÇR’ÒVæW‡V7FVBÆöG7FFR"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢54U%B†fÇ6R“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–‡F‡&VBVÇR’Ò7F'F–ær6Æ÷6R"’ÂvWD7W'&VçEF‡&VD–B‚’“°Ð¢ÐÐ Ð¢4WFôÆö6²v‚fÆö6´w&„66W72“°Ð Ð¢–b†Õ÷ÔR’°Ð¢Õ÷ÔRÓå6WDæ÷F–g”fÆw2„ÕôÔTD”UdTåEôäôäõD”e’“°Ð¢Õ÷ÔRÓå6WDæ÷F–g•v–æF÷r„åTÄÂÂÂ“°Ð¢Õ÷ÔRå&VÆV6R‚“°Ð¢ÐÐ Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂæ6Æ÷6R‚“°Ð Ð¢–b†Õö%6WGF–æuWÖVçW2’°Ð¢6ÆVWW‚ƒSÂfÇ6R“°Ð¢54U%B‚Õö%6WGF–æuWÖVçW2“°Ð¢ÐÐ Ð¢&ööÂö6Æ÷6–ærÒF†—2Óä—5v–æF÷uf—6–&ÆR‚“°Ð Ð¢&ööÂ6fV†—7F÷'’ÒfÇ6S°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢–b‚ö6Æ÷6–ærbbvWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅW6R‡G'VR“°Ð¢ÐÐ Ð¢òò&÷'B7V"6V&6€Ð¢Õ÷7V'F—FÆW5&÷f–FW'2Óä&÷'B…7V'F—FÆW5F‡&VEG—R…5EEõ4T$4‚Â5EEôDõtäÄôB’“°Ð¢Õ÷væE7V'F—FÆW4F÷væÆöDF–ÆöräFô6ÆV"‚“°Ð¢Õ÷væE7V'F—FÆW4F÷væÆöDF–Æörå6†÷uv–æF÷r…5uô„”DR“°Ð Ð¢òò6fRÆ–&6²÷6—F–öàÐ¢–b‡2æd¶VW†—7F÷'’bb%VæF–ætf–ÆTFVÆWFR’°Ð¢–b†Õö%&VÖVÖ&W$f–ÆU÷2bbÕödVæDöe7G&VÒbbÕ÷Õ2’°Ð¢$TdU$Tä4UõD”ÔR'Dæ÷rÒ°Ð¢Õ÷Õ2ÓävWD7W'&VçE÷6—F–öâ‚g'Dæ÷r“°Ð¢–b‡'Dæ÷râ’°Ð¢$TdU$Tä4UõD”ÔR'DGW"Ò°Ð¢Õ÷Õ2ÓävWDGW&F–öâ‚g'DGW"“°Ð¢–b‡'Dæ÷rãÒ'DGW"ÇÂ'DGW"Ò'Dæ÷rÂSÄÂ’²òòBVæBöbf–ÆPÐ¢'Dæ÷rÒ°Ð¢ÐÐ¢ÐÐ¢2äÕ%RåWFFT7W'&VçDf–ÆU÷6—F–öâ‡'Dæ÷rÂG'VR“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBbbÕ÷EdD’’°Ð¢EdEôDôÔ”âEdDFöÖ–ã°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDFöÖ–â‚dEdDFöÖ–â’’’°Ð¢–b„EdDFöÖ–âÓÒEdEôDôÔ”åõF—FÆR’°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö6F–öã#°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚dÆö6F–öã"’’’°Ð¢EdEõõ4•D”ôâGfE÷6—F–öâÒ2äÕ%RävWD7W'&VçDEdE÷6—F–öâ‚“°Ð¢–b†GfE÷6—F–öâæÆÄEdDwV–B’°Ð¢GfE÷6—F–öâæÅF—FÆRÒÆö6F–öã"åF—FÆTçVÓ°Ð¢GfE÷6—F–öâçF–ÖV6öFRÒÆö6F–öã"åF–ÖT6öFS°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢òò6fRW‡FW&æÂ7V'F—FÆPÐ¢–b†uö$W‡FW&æÅ7V'F—FÆRbb%VæF–ætf–ÆTFVÆWFRb`Ð¢Õ÷7W'&VçE7V$–çWBç7V%7G&VÒbbÕ÷7W'&VçE7V$–çWBç7V%7G&VÒÓävWEF‚‚’ä—4V×G’‚’’°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b‡2æ$WFõ6fTF÷væÆöFVE7V'F—FÆW2’°Ð¢57G&–ærF—$'VffW#°Ð¢Å5E5E"F—"ÒçVÆÇG#°Ð¢–b‚2ç7G%7V'F—FÆUF‡2ä—4V×G’‚’’°Ð¢WFò7F'BÒ2ç7G%7V'F—FÆUF‡2äÆVgBƒ"“°Ð¢–b‡7F'BÒõB‚"â"’bb7F'BÒõB‚"ã²"’’°Ð¢–çB÷2Ò°Ð¢F—"ÒF—$'VffW"Ò2ç7G%7V'F—FÆUF‡2åFö¶Væ—¦R…õB‚#²"’Â÷2“°Ð¢ÐÐ¢ÐÐ¢7V'F—FÆW56fR†F—"ÂG'VR“°Ð¢ÐÐ¢ÐÐ Ð¢–b‡2æd¶VW†—7F÷'’bb%VæF–ætf–ÆTFVÆWFR’°Ð¢6fV†—7F÷'’ÒG'VS°Ð¢ÐÐ¢ÐÐ Ð¢Õ4r×6s°Ð¢òòW&vR÷76–&ÆRVWVVBw&‚WfVçG0Ð¢v†–ÆR…VV´ÖW76vR‚f×6rÂçVÆÇG"ÂtÕôu$„äõD”e’ÂtÕôu$„äõD”e’ÂÕõ$TÔõdR’’°Ð¢E$4R„Â%W&vVBVWVVBw&‚WfVçEÆâ"“°Ð¢ÐÐ¢–b…VV´ÖW76vR‚f×6rÂçVÆÇG"ÂtÕõ$U4UEôDUd”4RÂtÕõ$U4UEôDUd”4RÂÕõ$TÔõdR’’°Ð¢E$4R„Â%W&vVBVWVVBtÕõ$U4UEôDUd”4UÆâ"“°Ð¢ÐÐ Ð¢òòFVÆ’6†÷v–ærWFòÖ†–FFVâ6öçG&öÇ2–bæWrÖVF–—2VWVV@Ð¢–b†$æW‡D—5VWVVB’°Ð¢Õö6öçG&öÇ2äFVÆ•6†÷tæ÷DÆöFVB‡G'VR“°Ð¢ÒVÇ6R°Ð¢Õö6öçG&öÇ2äFVÆ•6†÷tæ÷DÆöFVB†fÇ6R“°Ð¢ÐÐ Ð¢4FÄÆ—7CÄÕ4sâ÷7GöæVF×6s°Ð Ð¢òò&÷'B–bÆöF–æpÐ¢&ööÂ$w&…FW&Ö–æFVBÒfÇ6S°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôD”är’°Ð¢òòFVÆÂ÷VäÖVF–&—fFR‚’F†BvRvçBFò&÷'@Ð¢Õöd÷Væ–æt&÷'FVBÒG'VS°Ð Ð¢6WDÆöE7FFR„ÔÅ3£¤$õ%D”är“°Ð Ð¢E$4R…õB‚$ÖVF–—27F–ÆÂÆöF–ærâ&÷'F–ærw&‚åÆâ"’“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–ÒæVVBFò&÷'Bw&‚7&VF–öâ"’“°Ð¢ÐÐ Ð¢òò6Æ÷6R–â6öææV7F–öâW'&÷"F–ÆöpÐ¢–b†ÖVF–G—W4W'&÷$FÆr’°Ð¢ÖVF–G—W4W'&÷$FÆrÓå6VæDÖW76vR…tÕôU…DU$äÄ4Äõ4RÂÂ“°Ð¢òòv—BF–ÆÂW'&÷"F–Æör†2&VVâ6Æ÷6V@Ð¢4WFôÆö6²Æ6²‚fÆö6´ÖöFÄF–Æör“°Ð¢ÐÐ Ð¢òò&÷'B7W'&VçBw&‚F6°Ð¢–b†Õ÷t"’°Ð¢–b‚Õ÷Ôõ’°Ð¢Õ÷ÔõÒÕ÷t#°Ð¢–b‚Õ÷Ôõ’°Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$bÐ¢–b†Õ÷ÔõÒ$b’°Ð¢'&V³°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð¢ÐÐ¢ÐÐ¢–b†Õ÷Ôõ’°Ð¢Õ÷ÔõÓä&÷'D÷W&F–öâ‚“°Ð¢ÐÐ¢Õ÷t"Óä&÷'B‚“²òòDôDó¢Æö6²öâw&‚ö&¦V7G26öÖV†÷rÂF†—2—2æ÷BF‡&VB6fPÐ¢ÐÐ¢–b†Õ÷t%÷&Wf–Wr’°Ð¢Õ÷t%÷&Wf–WrÓä&÷'B‚“°Ð¢ÐÐ Ð¢–b†Õö$÷VæVEF‡&÷Vv…F‡&VBbbÕ÷w&…F‡&VBbbÕ÷w&…F‡&VBÓæÕö…F‡&VB’°Ð¢&Vv–åv—D7W'6÷"‚“°Ð¢Etõ$BGuv—C°Ð¢„äDÄR†æFÆRÒÕöWd÷Vå&—fFTf–æ—6†VC°Ð¢TÄôätÄôärv—FGW"ÒcTÄÃ°Ð¢TÄôätÄôärF6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢&ööÂ¶–ÆÇ&ö6W72ÒG'VS°Ð¢&ööÂ&ö6W76×6rÒG'VS°Ð¢&ööÂW‡FVæFVGv—BÒfÇ6S°Ð¢–b†ö6Æ÷6–ær’°Ð¢v—FGW"³Ò#TÄÃ°Ð¢ÐÐ¢–çBÒÒ°Ð¢&ööÂf–ÆUö6†V6¶VBÒfÇ6S°Ð¢v†–ÆR‡&ö6W76×6r’°Ð¢Guv—BÒ×6uv—Df÷$×VÇF—ÆTö&¦V7G2ƒÂf†æFÆRÂdÅ4RÂ„Etõ$B—7FC£¦Ö–â‡v—FGW"ÂSTÄÂ’Â5õõ5DÔU54tRÂ5õ4TäDÔU54tR“°Ð¢7v—F6‚†Guv—B’°Ð¢66Rt•Eôô$¤T5Eó Ð¢E$4R…õB‚$w&‚&÷'B7V66W76gVÅÆâ"’“°Ð¢¶–ÆÇ&ö6W72ÒfÇ6S²òòWfVçB†2&VVâ6–væÆÆV@Ð¢&ö6W76×6rÒfÇ6S°Ð¢$w&…FW&Ö–æFVBÒG'VS°Ð¢'&V³°Ð¢66Rt•Eôô$¤T5Eó² Ð¢òòvR†fRÖW76vRÒVV²æBF—7F6‚—@Ð¢ÒÒ°Ð¢v†–ÆR‚‡Ò²²Â2’bbVV´ÖW76vR‚f×6rÂ„…täB’ÓÂÂÂÕõ$TÔõdR’’°Ð¢–b†×6ræÖW76vRÓÒtÕõT•B’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R–b†×6ræÖW76vRÓÒ’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôu$„äõD”e’ÇÂ×6ræÖW76vRÓÒtÕõ$U4UEôDUd”4R’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕõõ5DõTâÇÂ×6ræÖW76vRÓÒtÕôõTäd”ÄTB’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôõ4Eô„”DR’°Ð¢F—7F6„ÖW76vR‚f×6r“°Ð¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôõ4EôE$r’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕô4Äõ4R’°Ð¢–b†$æW‡D—5VWVVB’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R°Ð¢òò÷7GöæPÐ¢÷7GöæVF×6räFD†VB†×6r“°Ð¢ÐÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕõ5•44ôÔÔäBÇÂ×6ræÖW76vRÓÒtÕô4ôÔÔäBÇÂ×6ræÖW76vRÓÒtÕôD•5Ä”4„ätRÇÂ×6ræÖW76vRãÒtÕôbb×6ræÖW76vRÂtÕô²’°Ð¢òò÷7GöæPÐ¢÷7GöæVF×6räFD†VB†×6r“°Ð¢ÒVÇ6R°Ð¢–b†×6ræÖW76vRÒtÕõ”åBbb×6ræÖW76vRÒtÕô´U•Ubb×6ræÖW76vRÒtÕôÔõU4TÔõdRbb×6ræÖW76vRÒ†36R’°Ð¢E$4R…õB‚$F—7F6‚tÒGW&–ærw&‚&÷'C¢×6sÓ‚W‚wÒVÆÇRÇÒVÆEÆâ"’Â×6ræÖW76vRÂ×6rçu&ÒÂ×6ræÅ&Ò“°Ð¢ÐÐ¢G&ç6ÆFTÖW76vR‚f×6r“°Ð¢F—7F6„ÖW76vR‚f×6r“°Ð¢ÐÐ¢ÐÐ¢'&V³°Ð¢66Rt•EõD”ÔTõUC Ð¢'&V³°Ð¢FVfVÇC¢òòVæW‡V7FVBf–ÇW&PÐ¢&ö6W76×6rÒfÇ6S°Ð¢'&V³°Ð¢ÐÐ¢–b‡&ö6W76×6r’°Ð¢54U%B†Õ÷t"ÇÂÕ÷t%÷&Wf–Wr“°Ð¢TÄôätÄôär7W"ÒvWEF–6´6÷VçCcB‚“°Ð¢–b‡F6¶–ÆÂâ7W"’°Ð¢v—FGW"ÒF6¶–ÆÂÒ7W#°Ð¢ÒVÇ6R°Ð¢–b‚f–ÆUö6†V6¶VB’°Ð¢f–ÆUö6†V6¶VBÒG'VS°Ð¢–b‚Æ7D÷Väf–ÆRä—4V×G’‚’bbF…WF–Ç3£¤—5U$Â†Æ7D÷Väf–ÆR’’°Ð¢òò6†V6²f–ÆRW†—7Fæ6RÂF†—26†÷VÆB7–âW†F@Ð¢TÄôätÄôärF3ÒvWEF–6´6÷VçCcB‚“°Ð¢5F‚F‚Ò5F‚†Æ7D÷Väf–ÆR“°Ð¢&ööÂW†—7G2ÒF‚äf–ÆTW†—7G2‚“°Ð¢TÄôätÄôärF3"ÒvWEF–6´6÷VçCcB‚“°Ð¢–b‡F3"ÒF3ãÒS’°Ð¢òòFVÆ’—2Æ–¶VÇ’6W6VB'’VæF–ær”ðÐ¢–b‚ö6Æ÷6–ær’°Ð¢Õö6Æ÷6–æv×6rÒÂ$f–ÆR6Æ÷6RFVÆ’—26W6VB'’†&FG&—fR&W7VÖ–ærg&öÒ6ÆVWÖöFR#°Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR†Õö6Æ÷6–æv×6r“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–Òf–ÆR6Æ÷6RFVÆ’—26W6VB'’†&FG&—fR&W7VÖ–ærg&öÒ6ÆVWÖöFR"’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b†W†—7G2’°Ð¢v—FGW"ÒSTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢6öçF–çVS°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†W‡FVæFVGv—BÇÂÕödgVÆÅ67&VVâÇÂ2æ„Ö7FW%væBÇÂ†–&W&æF–ærÇÂö6Æ÷6–ær’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b†W‡FVæFVGv—Bbb7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢–b„”E”U2ÓÒg„ÖW76vT&÷‚„Â$—BÆöö·2Æ–¶RF†Rf–ÇFW"w&‚Ö–v‡B&RFVFÆö6¶VBåÆåÆä6Æ–6²”U2Fò7V&Ö—B7&6‚&W÷'BåÆä6Æ–6²äòFòFW&Ö–æFRF†RÆ–W"&ö6W72â"ÂÔ%ô”4ôäU„4ÄÔD”ôâÂÔ%õ”U4äòÂ’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢ÐÐ¢6VæF–`Ð¢ÒVÇ6R°Ð¢57G&–ærF–ÖV÷WF×6s°Ð¢–b‡2æ”E5f–FVõ&VæFW&W%G—RÓÒd”E$äEEôE5ôÔEe"’°Ð¢F–ÖV÷WF×6rÒÂ%F–ÖV÷WBv†–ÆR&÷'F–ærf–ÇFW"w&‚7&VF–öâåÆåÆä–bf–ÆW2ÆöB6Æ÷vÇ’v—F‚ÖEe"Â–÷R6†÷VÆB6†ævRF—F†W&–ær–âÖGg"6WGF–æw2„W'&÷"F–fgW6–öâ—2'&ö¶VâöâÔBuR’åÆåÆä6Æ–6²”U2FòFW&Ö–æFRÆ–W"&ö6W72â6Æ–6²äòFòv—BÆöævW"‡WFòR6V6öæG2’â#°Ð¢ÒVÇ6R°Ð¢F–ÖV÷WF×6rÒÂ%F–ÖV÷WBv†–ÆR&÷'F–ærf–ÇFW"w&‚7&VF–öâåÆåÆä6Æ–6²”U2FòFW&Ö–æFRÆ–W"&ö6W72â6Æ–6²äòFòv—BÆöævW"‡WFòR6V6öæG2’â#°Ð¢ÐÐ¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–ÒF–ÖV÷WBv†Vâ&÷'F–ærf–ÇFW"w&‚7&VF–öâ"’“°Ð¢ÐÐ¢–b„”E”U2ÓÒg„ÖW76vT&÷‚‡F–ÖV÷WF×6rÂÔ%ô”4ôäU„4ÄÔD”ôâÂÔ%õ”U4äòÂ’’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R°Ð¢W‡FVæFVGv—BÒG'VS°Ð¢v—FGW"ÒSTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†¶–ÆÇ&ö6W72Ð¢°Ð¢òò&÷'F–ærw&‚f–ÆV@Ð¢E$4R…õB‚$f–ÆVBFò&÷'Bw&‚7&VF–öâåÆâ"’“°Ð¢f÷&6T6Æ÷6U&ö6W72‚“°Ð¢ÐÐ¢VæEv—D7W'6÷"‚“°Ð¢ÒVÇ6R°Ð¢òò&÷'F–ærw&‚f–ÆV@Ð¢E$4R…õB‚$f–ÆVBFò&÷'Bw&‚7&VF–öâåÆâ"’“°Ð¢f÷&6T6Æ÷6U&ö6W72‚“°Ð¢ÐÐ Ð¢òòW&vR÷76–&ÆRVWVVBöäf–ÆU÷7D÷VæÖVF–‚Ð¢–b…VV´ÖW76vR‚f×6rÂÕö…væBÂtÕõõ5DõTâÂtÕõõ5DõTâÂÕõ$TÔõdRÂÕôäõ””TÄB’’°Ð¢g&VR‚„÷VäÖVF–FF¢–×6ræÅ&Ò“°Ð¢ÐÐ¢òòW&vR÷76–&ÆRVWVVBöä÷VäÖVF–f–ÆVB‚Ð¢–b…VV´ÖW76vR‚f×6rÂÕö…væBÂtÕôõTäd”ÄTBÂtÕôõTäd”ÄTBÂÕõ$TÔõdRÂÕôäõ””TÄB’’°Ð¢g&VR‚„÷VäÖVF–FF¢–×6ræÅ&Ò“°Ð¢ÐÐ Ð¢òò&÷'Bf–æ—6†VBÂVç6WBF†RfÆpÐ¢Õöd÷Væ–æt&÷'FVBÒfÇ6S°Ð¢ÐÐ Ð¢òòvR&RöâF†RvÐ¢Õö%6WGF–æuWÖVçW2ÒG'VS°Ð¢6WDÆöE7FFR„ÔÅ3£¤4Äõ4”är“°Ð Ð¢–b†Õ÷t%÷&Wf–Wr’°Ð¢&Wf–Wuv–æF÷t†–FR‚“°Ð¢Õö%W6U6VVµ&Wf–WrÒfÇ6S°Ð¢ÐÐ Ð¢òòWFFRT’f÷"7F÷VB7FFPÐ¢òòF†Rw&‚—G6VÆb—27F÷VB–â6Æ÷6TÖVF–&—fFR‚’Âv†–6‚—26ÆÆVB&VÆ÷r'’w&‚F‡&VB†÷"F—&V7FÇ’Ð¢öåÆ•7F÷‡G'VR“°Ð Ð¢òò6ÆV"ç’7F—fR÷6BÖW76vW0Ð¢òöÕôõ4Bä6ÆV$ÖW76vR‚“°Ð Ð¢òòVç7W&RF†RG–æÖ–6ÆÇ’FFVBÖVçR—FV×2&R6ÆV&VBæBÆÂ&VfW&Væ6W0Ð¢òòöâö&¦V7G2&VÆöæv–ærFòF†RF—&V7E6†÷rw&‚F†W’Ö–v‡B†öÆB&Rg&VVBàÐ¢òòæ÷FRF†BvRæVVBFò&R–â6Æ÷6–ær7FFRÇ&VG’v†VâFö–ærF†@Ð¢–b†Õö…væB’°Ð¢6WGWf–ÇFW'57V$ÖVçR‚“°Ð¢6WGWVF–õ7V$ÖVçR‚“°Ð¢6WGW7V'F—FÆW57V$ÖVçR‚“°Ð¢6WGWf–FVõ7G&V×57V$ÖVçR‚“°Ð¢6WGW§V×Fõ7V$ÖVçW2‚“°Ð¢ÐÐ Ð¢Õö%6WGF–æuWÖVçW2ÒfÇ6S°Ð Ð¢òò–æ—F–FRw&‚FW7G'V7F–öàÐ¢&ööÂW6WF‡&VBÒÕö$÷VæVEF‡&÷Vv…F‡&VBbbÕ÷w&…F‡&VBbbÕ÷w&…F‡&VBÓæÕö…F‡&VBbb$w&…FW&Ö–æFVC°Ð¢–b‡W6WF‡&VB’°Ð¢òòV—F†W"÷Væ–ær÷"6Æ÷6–ær†2Fò&R&Æö6¶VBFò&WfVçB&VVçFW&–ærF†VÒÂ6Æ÷6–ær—2F†R&WGFW"6†ö–6PÐ¢–b‚ÕöWd6Æ÷6U&—fFTf–æ—6†VBå&W6WB‚’ÇÂÕ÷w&…F‡&VBÓå÷7EF‡&VDÖW76vR„4w&…F‡&VC£¥DÕô4Äõ4RÂ…u$Ò“Â„Å$Ò“’’°Ð¢Etõ$BÆ7FW'&÷"ÒvWDÆ7DW'&÷"‚“°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–Òw&‡F‡&VBW'&÷"VB"’ÂÆ7FW'&÷"“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢W6WF‡&VBÒfÇ6S°Ð¢54U%B†fÇ6R“°Ð¢ÐÐ¢ÐÐ¢–b‡W6WF‡&VB’°Ð¢„äDÄR†æFÆRÒÕöWd6Æ÷6U&—fFTf–æ—6†VC°Ð¢Etõ$BGuv—C°Ð¢TÄôätÄôärv—FGW"ÒcTÄÃ°Ð¢TÄôätÄôärF6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢&ööÂ¶–ÆÇ&ö6W72ÒG'VS°Ð¢&ööÂ&ö6W76×6rÒG'VS°Ð¢&ööÂW‡FVæFVGv—BÒfÇ6S°Ð¢–b†ö6Æ÷6–ær’°Ð¢v—FGW"³Ò#TÄÃ°Ð¢ÐÐ¢–çBÒÒ°Ð¢&ööÂf–ÆUö6†V6¶VBÒfÇ6S°Ð¢v†–ÆR‡&ö6W76×6r’°Ð¢òòF†—2æVVG2FòBÆV7Bv¶Rf÷"5õ4TäDÔU54tR&V6W6R÷F†W'v—6Rw&‚vöâwBFW&Ö–æFRVçF–ÂF†—2F–ÖW2÷WBàÐ¢òò—BÇ6òæVVG2VV´ÖW76vRÂ&V6W6RF†BG&–vvW'2–çFW&æÂF—7F6‚öb6W'F–âVæF–ærÖW76vW2àÐ¢òòtÕôtUD”4ôâƒƒvb’ÖW76vRvWG26VæBGW&–ær&VÆV6Röbw&‚'V–ÆFW"æBF†B&Æö6·2Ö–âF‡&VBVçF–ÂF†B×6r—2&ö6W76VBàÐ¢òòF†RtÕôtUD”4ôâ×6rvWG26VæBv†Vâ&Væ†æ6VBF6¶&"fVGW&W2"—2Væ&ÆVBÂgFW"V6‚7FFR6†ævR÷"&öw&W72WFFR6ÆÂW6–ærÕ÷F6¶&$Æ—7@Ð¢Guv—BÒ×6uv—Df÷$×VÇF—ÆTö&¦V7G2ƒÂf†æFÆRÂdÅ4RÂ„Etõ$B—7FC£¦Ö–â‡v—FGW"ÂSTÄÂ’Â5õõ5DÔU54tRÂ5õ4TäDÔU54tR“°Ð¢7v—F6‚†Guv—B’°Ð¢66Rt•Eôô$¤T5Eó Ð¢&ö6W76×6rÒfÇ6S²òòWfVçB&V6V—fV@Ð¢¶–ÆÇ&ö6W72ÒfÇ6S°Ð¢'&V³°Ð¢66Rt•Eôô$¤T5Eó² Ð¢ÒÒ°Ð¢v†–ÆR‚‡Ò²²Â2’bbVV´ÖW76vR‚f×6rÂ„…täB’ÓÂÂÂÕõ$TÔõdR’’°Ð¢–b†×6ræÖW76vRÓÒtÕõT•B’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R–b†×6ræÖW76vRÓÒ’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôu$„äõD”e’ÇÂ×6ræÖW76vRÓÒtÕõ$U4UEôDUd”4R’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôõ4Eô„”DR’°Ð¢F—7F6„ÖW76vR‚f×6r“°Ð¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕôõ4EôE$r’°Ð¢òò–væ÷&PÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕô4Äõ4R’°Ð¢–b†$æW‡D—5VWVVB’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R°Ð¢òò÷7GöæPÐ¢÷7GöæVF×6räFD†VB†×6r“°Ð¢ÐÐ¢ÒVÇ6R–b†×6ræÖW76vRÓÒtÕõ5•44ôÔÔäBÇÂ×6ræÖW76vRÓÒtÕô4ôÔÔäBÇÂ×6ræÖW76vRÓÒtÕôD•5Ä”4„ätRÇÂ×6ræÖW76vRãÒtÕôbb×6ræÖW76vRÂtÕô²’°Ð¢òò÷7GöæPÐ¢÷7GöæVF×6räFD†VB†×6r“°Ð¢ÒVÇ6R°Ð¢–b†×6ræÖW76vRÒtÕõ”åBbb×6ræÖW76vRÒtÕô´U•Ubb×6ræÖW76vRÒtÕôÔõU4TÔõdRbb×6ræÖW76vRÒ†36R’°Ð¢E$4R…õB‚$F—7F6‚tÒGW&–ærw&‚6Æ÷6S¢×6sÓ‚W‚wÒVÆÇRÇÒVÆEÆâ"’Â×6ræÖW76vRÂ×6rçu&ÒÂ×6ræÅ&Ò“°Ð¢ÐÐ¢G&ç6ÆFTÖW76vR‚f×6r“°Ð¢F—7F6„ÖW76vR‚f×6r“°Ð¢ÐÐ¢ÐÐ¢'&V³°Ð¢66Rt•EõD”ÔTõUC Ð¢–b‚W‡FVæFVGv—B’°Ð¢TÄôätÄôärF6æ÷rÒvWEF–6´6÷VçCcB‚“°Ð¢–b‡F6æ÷râF6¶–ÆÂbbF6æ÷rÒF6¶–ÆÂãÒ#TÄÂ’°Ð¢W‡FVæFVGv—BÒG'VS°Ð¢v—FGW"ÒCTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢6öçF–çVS°Ð¢ÐÐ¢ÐÐ¢'&V³°Ð¢FVfVÇC Ð¢&ö6W76×6rÒfÇ6S°Ð¢'&V³°Ð¢ÐÐ Ð¢–b‡&ö6W76×6r’°Ð¢TÄôätÄôär7W"ÒvWEF–6´6÷VçCcB‚“°Ð¢–b‡F6¶–ÆÂâ7W"’°Ð¢v—FGW"ÒF6¶–ÆÂÒ7W#°Ð¢ÒVÇ6R°Ð¢–b‚f–ÆUö6†V6¶VB’°Ð¢f–ÆUö6†V6¶VBÒG'VS°Ð¢–b‚Æ7D÷Väf–ÆRä—4V×G’‚’bbF…WF–Ç3£¤—5U$Â†Æ7D÷Väf–ÆR’’°Ð¢òò6†V6²f–ÆRW†—7Fæ6RÂF†—26†÷VÆB7–âW†F@Ð¢TÄôätÄôärF3ÒvWEF–6´6÷VçCcB‚“°Ð¢5F‚F‚Ò5F‚†Æ7D÷Väf–ÆR“°Ð¢&ööÂW†—7G2ÒF‚äf–ÆTW†—7G2‚“°Ð¢TÄôätÄôärF3"ÒvWEF–6´6÷VçCcB‚“°Ð¢–b‡F3"ÒF3ãÒS’°Ð¢òòFVÆ’—2Æ–¶VÇ’6W6VB'’VæF–ær”ðÐ¢–b‚ö6Æ÷6–ær’°Ð¢Õö6Æ÷6–æv×6rÒÂ$f–ÆR6Æ÷6RFVÆ’—26W6VB'’†&FG&—fR&W7VÖ–ærg&öÒ6ÆVWÖöFR#°Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR†Õö6Æ÷6–æv×6r“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–Òf–ÆR6Æ÷6RFVÆ’—26W6VB'’†&FG&—fR&W7VÖ–ærg&öÒ6ÆVWÖöFR"’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b†W†—7G2’°Ð¢v—FGW"ÒSTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢6öçF–çVS°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†W‡FVæFVGv—BÇÂÕödgVÆÅ67&VVâÇÂ2æ„Ö7FW%væBÇÂ†–&W&æF–ærÇÂö6Æ÷6–ær’°Ð¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b†W‡FVæFVGv—Bbb7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢–b„”E”U2ÓÒg„ÖW76vT&÷‚„Â$—BÆöö·2Æ–¶RF†Rf–ÇFW"w&‚Ö–v‡B&RFVFÆö6¶VBåÆåÆä6Æ–6²”U2Fò7V&Ö—B7&6‚&W÷'BåÆä6Æ–6²äòFòFW&Ö–æFRF†RÆ–W"&ö6W72â"ÂÔ%ô”4ôäU„4ÄÔD”ôâÂÔ%õ”U4äòÂ’’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢ÐÐ¢6VæF–`Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R°Ð¢–b‚Õ÷t"bbÕ÷t%÷&Wf–Wr’°Ð¢v—FGW"ÒSTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢W‡FVæFVGv—BÒG'VS°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢57G&–ærF–ÖV÷WF×6rÒÂ%F–ÖV÷WBv†Vâ6Æ÷6–ærf–ÇFW"w&‚åÆåÆä6Æ–6²”U2FòFW&Ö–æFRÆ–W"&ö6W72â6Æ–6²äòFòv—BÆöævW"‡WFòR6V6öæG2’â#°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–ÒF–ÖV÷WBv†Vâ6Æ÷6–ærf–ÇFW"w&‚"’“°Ð¢ÐÐ¢–b„”E”U2ÓÒg„ÖW76vT&÷‚‡F–ÖV÷WF×6rÂÔ%ô”4ôäU„4ÄÔD”ôâÂÔ%õ”U4äòÂ’’°Ð¢&ö6W76×6rÒfÇ6S°Ð¢ÒVÇ6R°Ð¢W‡FVæFVGv—BÒG'VS°Ð¢v—FGW"ÒSTÄÃ°Ð¢F6¶–ÆÂÒvWEF–6´6÷VçCcB‚’²v—FGW#°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢–b†¶–ÆÇ&ö6W72’°Ð¢E$4R…õB‚$f–ÆVBFò6Æ÷6Rf–ÇFW"w&‚F‡&VBåÆâ"’“°Ð¢f÷&6T6Æ÷6U&ö6W72‚“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢6Æ÷6TÖVF–&—fFR‚“°Ð¢ÐÐ Ð¢òòW&vR÷76–&ÆRVWVVBw&‚WfVçG0Ð¢v†–ÆR…VV´ÖW76vR‚f×6rÂçVÆÇG"ÂtÕôu$„äõD”e’ÂtÕôu$„äõD”e’ÂÕõ$TÔõdR’’°Ð¢E$4R„Â%W&vVBVWVVBw&‚WfVçEÆâ"“°Ð¢ÐÐ¢–b…VV´ÖW76vR‚f×6rÂçVÆÇG"ÂtÕõ$U4UEôDUd”4RÂtÕõ$U4UEôDUd”4RÂÕõ$TÔõdR’’°Ð¢E$4R„Â%W&vVBVWVVBtÕõ$U4UEôDUd”4UÆâ"“°Ð¢ÐÐ Ð¢òòw&‚—2FW7G&÷–VBÂWFFR7GVf`Ð¢öäf–ÆU÷7D6Æ÷6VÖVF–†$æW‡D—5VWVVB“°Ð Ð¢–b‡6fV†—7F÷'’’°Ð¢2äÕ%Råw&—FT7W'&VçDVçG'’‚“°Ð¢ÐÐ¢2äÕ%Ræ7W'&VçE÷&fUö†6‚äV×G’‚“°Ð Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤6Æ÷6TÖVF–Ò6ö×ÆWFVB"’“°Ð¢ÐÐ¢dÅU4…ôÄôttU"‚“°Ð Ð¢v†–ÆR‚÷7GöæVF×6rä—4V×G’‚’’°Ð¢×6rÒ÷7GöæVF×6rå&VÖ÷fT†VB‚“°Ð¢57G&–ær×6w7G#°Ð¢×6w7G"äf÷&ÖB„Â%÷7GöæVBtÒgFW"w&‚6Æ÷6S¢×6sÓ‚W‚wÒVÆÇRÇÒVÆB‡VæF–ævÖVF–ÒVB•Æâ"Â×6ræÖW76vRÂ×6rçu&ÒÂ×6ræÅ&ÒÂ$æW‡D—5VWVVB“°Ð¢E$4R†×6w7G"“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr†×6w7G"“°Ð¢ÐÐ¢÷7DÖW76vR†×6ræÖW76vRÂ×6rçu&ÒÂ×6ræÅ&Ò“°Ð¢ÐÐ Ð¢E$4R…õB‚$6Æ÷6RÖVF–6ö×ÆWFVEÆâ"’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7F'EGVæW%66â„4WFõG#ÅGVæW%66äFFâE4BÐ§°Ð¢òò&VÖ÷fRF†RöÆB–æfòGW&–ærF†R66àÐ¢–b†Õ÷Ed%7FFR’°Ð¢Õ÷Ed%7FFRÓå&W6WB‚“°Ð¢ÐÐ¢Õ÷væD–æfô&"å&VÖ÷fTÆÄÆ–æW2‚“°Ð¢Õ÷væDæf–vF–öä&"æÕöæfFÆrå6WD6†ææVÄ–æfôf–Æ&ÆR†fÇ6R“°Ð¢&V6Æ4Æ–÷WB‚“°Ð¢÷Vå6WGWv–æF÷uF—FÆR‚“°Ð Ð¢–b†Õ÷w&…F‡&VBbbÕ÷w&…F‡&VBÓæÕö…F‡&VB’°Ð¢Õ÷w&…F‡&VBÓå÷7EF‡&VDÖW76vR„4w&…F‡&VC£¥DÕõETäU%õ44âÂ…u$Ò“Â„Å$Ò—E4BäFWF6‚‚’“°Ð¢ÒVÇ6R°Ð¢FõGVæW%66â‡E4B“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7F÷GVæW%66â‚Ð§°Ð¢Õö%7F÷GVæW%66âÒG'VS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥7F'D†VFÆW74Ed%66â‚Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢Õö†VFÆW74Ed%66ä6†ææVÇ2æ6ÆV"‚“°Ð Ð¢4WFõG#ÅGVæW%66äFFâE4B„DT%TuôäUrGVæW%66äFF“°Ð¢E4BÓä‡væBÒÕö…væC°Ð¢E4BÓäg&WVVæ7•7F'BÒ2æ6ÖFÆäEd%66âçVÄg&WVVæ7•7F'C°Ð¢E4BÓäg&WVVæ7•7F÷Ò2æ6ÖFÆäEd%66âçVÄg&WVVæ7•7F÷°Ð¢òò&æGv–GF‚—2´‡¢–âGVæW%66äFFæBÔ‡¢–âF†R&öf–ÆRâF†—2—2F†PÐ¢òò6ÖR6öçfW'6–öâ5GVæW%66äFÆrÖ¶W2v†Vâ—BÆöG2—G2f–VÆG2Â6òÐ¢òò†VFÆW72'VâæBF–Æör'Vâ66â–FVçF–6ÆÇ’f÷"–FVçF–6Â6WGF–æw2àÐ¢E4BÓä&æGv–GF‚Ò2æ6ÖFÆäEd%66âçVÄ&æGv–GF‚ò2æ6ÖFÆäEd%66âçVÄ&æGv–GF€Ð¢¢…TÄôär—2æ”$D&æGv–GF‚¢°Ð¢E4BÓå7–Ö&öÅ&FRÒ2æ6ÖFÆäEd%66âçVÅ7–Ö&öÅ&FRò2æ6ÖFÆäEd%66âçVÅ7–Ö&öÅ&FPÐ¢¢…TÄôär—2æ”$D7–Ö&öÅ&FS°Ð¢E4BÓäöfg6WBÒ2æd$DW6Töfg6WBò2æ”$Döfg6WB¢°Ð Ð¢7F'EGVæW%66â‡E4B“°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öä†VFÆW7566äæWt6†ææVÂ…u$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢–b‚Õö$†VFÆW74Ed%66â’°Ð¢&WGW&âdÅ4S°Ð¢ÐÐ Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢6öç7B6—¦U÷BÖ„6†ææVÇ4çVÒÒ”Eôäd”tDUô¥TÕDõõ5T$•DTÕôTäBÒ”Eôäd”tDUô¥TÕDõõ5T$•DTÕõ5D%B²°Ð Ð¢G'’°Ð¢4$D6†ææVÂ6†ææVÂ‚„Å5E5E"–Å&Ò“°Ð¢òòF†RF–ÆörÆ–W2F†—2f–ÇFW"2—Bf–ÆÇ2—G2Æ—7B&F†W"F†â@Ð¢òò6fRF–ÖRÂ6òÇ’—B†W&RFöòàÐ¢–b‚2æd$D–væ÷&TVæ7'—FVD6†ææVÇ2ÇÂ6†ææVÂä—4Væ7'—FVB‚’’°Ð¢–b†Õö†VFÆW74Ed%66ä6†ææVÇ2ç6—¦R‚’ÂÖ„6†ææVÇ4çVÒ’°Ð¢6†ææVÂå6WE&VdçVÖ&W"‚†–çB–Õö†VFÆW74Ed%66ä6†ææVÇ2ç6—¦R‚’“°Ð¢Õö†VFÆW74Ed%66ä6†ææVÇ2çW6…ö&6²†6†ææVÂ“°Ð¢ÐÐ¢ÐÐ¢Ò6F6‚„4W†6WF–öâ¢R’°Ð¢òò&V6÷&BF†Bv–ÆÂæ÷BFö¶Væ—6R—2G&÷VBæBF†R66â6öçF–çVW2ÀÐ¢òòv†–6‚—2v†B5GVæW%66äFÆs£¤öäæWt6†ææVÂFöW2v—F‚F†R6ÖRf–ÇW&RàÐ¢E$4R…õB‚"öGf'66ã¢f–ÆVBFò'6R66ææVB6†ææVÂ&V6÷&EÆâ"’“°Ð¢RÓäFVÆWFR‚“°Ð¢ÐÐ Ð¢&WGW&âE%TS°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öä†VFÆW7566äVæB…u$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢–b‚Õö$†VFÆW74Ed%66â’°Ð¢&WGW&âdÅ4S°Ð¢ÐÐ¢f–æ—6„†VFÆW74Ed%66â‚“°Ð¢&WGW&âE%TS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤f–æ—6„†VFÆW74Ed%66â‚Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢òòF†R6W&–Æ—¦W"F†RvV"–çFW&f6RW6W2Âæ÷B6V6öæB6÷’öb—C¢v†FWfW Ð¢òòöGf"ö6†ææVÇ2æ§6öâv÷VÆB6’&÷WBF†W6R6†ææVÇ2ÂF†—2f–ÆR6—2FöòàÐ¢6öç7B57G&–æt§6öâÒEd$6†ææVÇ5Fô¥4ôâ†Õö†VFÆW74Ed%66ä6†ææVÇ2“°Ð Ð¢&ööÂ%w&—GFVâÒfÇ6S°Ð¢–b‚2æ6ÖFÆäEd%66âç7G$÷WGWEF‚ä—4V×G’‚’’°Ð¢4f–ÆRf–ÆS°Ð¢4f–ÆTW†6WF–öâfS°Ð¢–b†f–ÆRä÷Vâ‡2æ6ÖFÆäEd%66âç7G$÷WGWEF‚ÀÐ¢4f–ÆS£¦ÖöFT7&VFRÂ4f–ÆS£¦ÖöFUw&—FRÂ4f–ÆS£§G—T&–æ'’ÂffR’’°Ð¢G'’°Ð¢f–ÆRåw&—FR‚„Å55E"–§6öâÂ§6öâävWDÆVæwF‚‚’“°Ð¢%w&—GFVâÒG'VS°Ð¢Ò6F6‚„4f–ÆTW†6WF–öâ¢fR’°Ð¢fRÓäFVÆWFR‚“°Ð¢ÐÐ¢f–ÆRä6Æ÷6R‚“°Ð¢ÐÐ¢ÐÐ Ð¢–b‚%w&—GFVâ’°Ð¢òòÆ÷6–ærF†R&W7VÇB6–ÆVçFÇ’v÷VÆBÆVfR6ÆÆW"Væ&ÆRFòFVÆÂàÐ¢òòV×G’66âg&öÒâVçw&—F&ÆRF‚àÐ¢E$4R…õB‚"öGf'66ã¢6÷VÆBæ÷Bw&—FRF†R&W7VÇBFòrW2uÆâ"’ÀÐ¢2æ6ÖFÆäEd%66âç7G$÷WGWEF‚ävWE7G&–ær‚’“°Ð¢ÐÐ Ð¢Õö$†VFÆW74Ed%66âÒfÇ6S°Ð¢÷7DÖW76vR…tÕô4Äõ4R“°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥6WD6†ææVÂ†–çBä6†ææVÂÐ§°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢…$U5TÅB‡"Ò5ôô³°Ð¢46öÕ•G#Ä”$DGVæW#âGVâÒÕ÷t#°Ð¢4$D6†ææVÂ¢6†ææVÂÒ2äf–æD6†ææVÄ'•&Vb†ä6†ææVÂ“°Ð Ð¢–b‡2æÕôEd$6†ææVÇ2æV×G’‚’bbä6†ææVÂÓÒ”åEôU%$õ"’°Ð¢‡"Ò5ôdÅ4S²òòÆÂ6†ææVÇ2†fR&VVâ6ÆV&VB÷"—B—2F†Rf—'7B7F'@Ð¢ÒVÇ6R–b‡GVâbb6†ææVÂbbÕ÷Ed%7FFRÓæ%6WD6†ææVÄ7F—fR’°Ð¢Õ÷Ed%7FFRÓå&W6WB‚“°Ð¢Õ÷væD–æfô&"å&VÖ÷fTÆÄÆ–æW2‚“°Ð¢Õ÷væDæf–vF–öä&"æÕöæfFÆrå6WD6†ææVÄ–æfôf–Æ&ÆR†fÇ6R“°Ð¢&V6Æ4Æ–÷WB‚“°Ð¢Õ÷Ed%7FFRÓæ%6WD6†ææVÄ7F—fRÒG'VS°Ð Ð¢òò6¶—â–çFW&ÖVF–FR¦ööÕf–FVõv–æF÷r‚’6ÆÇ2v†–ÆRF†RæWr6—¦R—27F&–Æ—¦VC Ð¢7v—F6‚‡2æ”E5f–FVõ&VæFW&W%G—R’°Ð¢66Rd”E$äEEôE5ôÔEe# Ð¢–b‡2æäEd%7F÷f–ÇFW$w&‚ÓÒEd%õ5DõôduôÅt•2’°Ð¢ÕöäÆö6¶VE¦ööÕf–FVõv–æF÷rÒ3°Ð¢ÒVÇ6R°Ð¢ÕöäÆö6¶VE¦ööÕf–FVõv–æF÷rÒ°Ð¢ÐÐ¢'&V³°Ð¢66Rd”E$äEEôE5ôUe%ô5U5DôÓ Ð¢ÕöäÆö6¶VE¦ööÕf–FVõv–æF÷rÒ°Ð¢'&V³°Ð¢FVfVÇC Ð¢ÕöäÆö6¶VE¦ööÕf–FVõv–æF÷rÒ°Ð¢ÐÐ¢–b…5T44TTDTB†‡"ÒGVâÓå6WD6†ææVÂ†ä6†ææVÂ’’’°Ð¢–b†‡"ÓÒ5ôdÅ4R’°Ð¢òò&RÖ7&VFRÆÀÐ¢ÕöäÆö6¶VE¦ööÕf–FVõv–æF÷rÒ°Ð¢÷7DÖW76vR…tÕô4ôÔÔäBÂ”Eôd”ÄUôõTäDUd”4R“°Ð¢&WGW&â‡#°Ð¢ÐÐ Ð¢Õ÷Ed%7FFRÓæ$7F—fRÒG'VS°Ð¢Õ÷Ed%7FFRÓç6†ææVÂÒ6†ææVÃ°Ð¢Õ÷Ed%7FFRÓç46†ææVÄæÖRÒ6†ææVÂÓävWDæÖR‚“°Ð Ð¢Õ÷væD–æfô&"å6WDÆ–æR…&W57G"„”E5ô”ädô$%ô4„ääTÂ’ÂÕ÷Ed%7FFRÓç46†ææVÄæÖR“°Ð¢&V6Æ4Æ–÷WB‚“°Ð Ð¢–b‡2æe&VÖVÖ&W%¦ööÔÆWfVÂbb†ÕödgVÆÅ67&VVâÇÂ—5¦ööÖVB‚’ÇÂ—4–6öæ–2‚’’’°Ð¢¦ööÕf–FVõv–æF÷r‚“°Ð¢ÐÐ¢Ö÷fUf–FVõv–æF÷r‚“°Ð Ð¢òòFBFV×÷&'’fÆrFòÆÆ÷rT5õd”DTõõ4•¤Uô4„ätTBWfVçBFò7F&–Æ—¦Rv–æF÷r6—¦PÐ¢òòf÷"R6V6öæG26–æ6RÆ–&6²7F'G0Ð¢Õö$ÆÆ÷uv–æF÷u¦ööÒÒG'VS°Ð¢Õ÷F–ÖW$öæUF–ÖRå7V'67&–&R…F–ÖW$öæUF–ÖU7V'67&–&W#£¤UDôd•EõD”ÔTõUBÂ·F†—5ÐÐ¢²Õö$ÆÆ÷uv–æF÷u¦ööÒÒfÇ6S²ÒÂS“°Ð Ð¢WFFT7W'&VçD6†ææVÄ–æfò‚“°Ð¢ÐÐ¢Õ÷Ed%7FFRÓæ%6WD6†ææVÄ7F—fRÒfÇ6S°Ð¢ÒVÇ6R°Ð¢‡"ÒUôd”Ã°Ð¢54U%B„dÅ4R“°Ð¢ÐÐ Ð¢&WGW&â‡#°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFT7W'&VçD6†ææVÄ–æfò†&ööÂ%6†÷tõ4Bò£ÒG'VR¢òÂ&ööÂ%6†÷t–æfô&"ò£ÒfÇ6R¢òÐ§°Ð¢6öç7B4$D6†ææVÂ¢6†ææVÂÒÕ÷Ed%7FFRÓç6†ææVÃ°Ð¢46öÕ•G#Ä”$DGVæW#âGVâÒÕ÷t#°Ð Ð¢–b‚Õ÷Ed%7FFRÓæ$–æfô7F—fRbb6†ææVÂbbGVâ’°Ð¢–b†Õ÷Ed%7FFRÓæ–æfôFFçfÆ–B‚’’°Ð¢Õ÷Ed%7FFRÓæ$&÷'D–æfòÒG'VS°Ð¢Õ÷Ed%7FFRÓæ–æfôFFævWB‚“°Ð¢ÐÐ¢Õ÷Ed%7FFRÓæ$&÷'D–æfòÒfÇ6S°Ð¢Õ÷Ed%7FFRÓæ$–æfô7F—fRÒG'VS°Ð¢Õ÷Ed%7FFRÓæ–æfôFFÒ7FC£¦7–æ2‡7FC£¦ÆVæ6ƒ£¦7–æ2Â·F†—2Â6†ææVÂÂGVâÂ%6†÷tõ4BÂ%6†÷t–æfô&%Ò°Ð¢Ed%7FFS£¤T•DFF–æfôFF°Ð¢–æfôFFæ‡"ÒGVâÓåWFFU4’‡6†ææVÂÂ–æfôFFäæ÷tæW‡B“°Ð¢–æfôFFæ%6†÷tõ4BÒ%6†÷tõ4C°Ð¢–æfôFFæ%6†÷t–æfô&"Ò%6†÷t–æfô&#°Ð¢–b†Õ÷Ed%7FFRbbÕ÷Ed%7FFRÓæ$&÷'D–æfòÐ¢°Ð¢÷7DÖW76vR…tÕôEd%ôT•EôDDõ$TE’“°Ð¢ÐÐ¢&WGW&â–æfôFF°Ð¢Ò“°Ð¢ÐÐ§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öä7W'&VçD6†ææVÄ–æfõWFFVB…u$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’°Ð¢&WGW&â°Ð¢ÐÐ Ð¢–b‚Õ÷Ed%7FFRÓæ$&÷'D–æfòbbÕ÷Ed%7FFRÓæ–æfôFFçfÆ–B‚’’°Ð¢WfVçDFW67&—F÷"bæ÷tæW‡BÒÕ÷Ed%7FFRÓäæ÷tæW‡C°Ð¢6öç7BWFò–æfôFFÒÕ÷Ed%7FFRÓæ–æfôFFævWB‚“°Ð¢æ÷tæW‡BÒ–æfôFFäæ÷tæW‡C°Ð Ð¢–b†–æfôFFæ‡"Ò5ôdÅ4R’°Ð¢òò6WBF–ÖW"FòWFFRF†R–æf÷2öæÇ’–b6†ææVÂ†2æ÷röæW‡BfÆpÐ¢F–ÖU÷BDæ÷s°Ð¢F–ÖR‚gDæ÷r“°Ð¢F–ÖU÷BDVÆ6RÒæ÷tæW‡BæGW&F–öâÒ‡Dæ÷rÒæ÷tæW‡Bç7F'EF–ÖR“°Ð¢–b‡DVÆ6RÂ’°Ð¢DVÆ6RÒ°Ð¢ÐÐ¢òòvR6WBW2FVÆ’FòÆWB6öÖR&ööÒf÷"F†R&öw&Ò–æf÷2Fò6†ævPÐ¢DVÆ6R³ÒS°Ð¢Õ÷F–ÖW$öæUF–ÖRå7V'67&–&R…F–ÖW$öæUF–ÖU7V'67&–&W#£¤Ed$”ädõõUDDRÀÐ¢·F†—5Ò²WFFT7W'&VçD6†ææVÄ–æfò†fÇ6RÂfÇ6R“²ÒÀÐ¢¢…T”åB—DVÆ6R“°Ð¢Õ÷væDæf–vF–öä&"æÕöæfFÆrå6WD6†ææVÄ–æfôf–Æ&ÆR‡G'VR“°Ð¢ÒVÇ6R°Ð¢Õ÷væDæf–vF–öä&"æÕöæfFÆrå6WD6†ææVÄ–æfôf–Æ&ÆR†fÇ6R“°Ð¢ÐÐ Ð¢57G&–ær46†ææVÄ–æfòÒÕ÷Ed%7FFRÓç46†ææVÄæÖS°Ð¢Õ÷væD–æfô&"å&VÖ÷fTÆÄÆ–æW2‚“°Ð¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ô4„ääTÂ’Â46†ææVÄ–æfò“°Ð Ð¢–b†–æfôFFæ‡"ÓÒ5ôô²’°Ð¢òòT•B–æf÷&ÖF–öâ'6VB6÷'&V7FÇÐ¢–b†–æfôFFæ%6†÷tõ4B’°Ð¢46†ææVÄ–æfòäVæDf÷&ÖB…õB‚"ÂW2‚W2ÒW2’"’Âæ÷tæW‡BæWfVçDæÖRävWE7G&–ær‚’Âæ÷tæW‡Bç7G%7F'EF–ÖRävWE7G&–ær‚’Âæ÷tæW‡Bç7G$VæEF–ÖRävWE7G&–ær‚’“°Ð¢ÐÐ Ð¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õD•DÄR’Âæ÷tæW‡BæWfVçDæÖR“°Ð¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õD”ÔR’Âæ÷tæW‡Bç7G%7F'EF–ÖR²õB‚"Ò"’²æ÷tæW‡Bç7G$VæEF–ÖR“°Ð Ð¢–b„æ÷tæW‡Bç&VçFÅ&F–ærãÒ’°Ð¢57G&–ær&VçE&F–æs°Ð¢–b‚æ÷tæW‡Bç&VçFÅ&F–ær’°Ð¢&VçE&F–æräÆöE7G&–ær„”E5ôäõõ$TåDÅõ$D”är“°Ð¢ÒVÇ6R°Ð¢&VçE&F–æräf÷&ÖB„”E5õ$TåDÅõ$D”ärÂæ÷tæW‡Bç&VçFÅ&F–ær“°Ð¢ÐÐ¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%õ$TåDÅõ$D”är’Â&VçE&F–ær“°Ð¢ÐÐ Ð¢–b‚æ÷tæW‡Bæ6öçFVçBä—4V×G’‚’’°Ð¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ô4ôåDTåB’Âæ÷tæW‡Bæ6öçFVçB“°Ð¢ÐÐ Ð¢57G&–ærFW67&—F–öâÒæ÷tæW‡BæWfVçDFW63°Ð¢–b‚æ÷tæW‡BæW‡FVæFVDFW67&—F÷'5FW‡Bä—4V×G’‚’’°Ð¢–b‚FW67&—F–öâä—4V×G’‚’’°Ð¢FW67&—F–öâ³ÒõB‚#²"“°Ð¢ÐÐ¢FW67&—F–öâ³Òæ÷tæW‡BæW‡FVæFVDFW67&—F÷'5FW‡C°Ð¢ÐÐ¢Õ÷væD–æfô&"å6WDÆ–æR…7G%&W2„”E5ô”ädô$%ôDU45$•D”ôâ’ÂFW67&—F–öâ“°Ð Ð¢f÷"†6öç7BWFòb—FVÒ¢æ÷tæW‡BæW‡FVæFVDFW67&—F÷'4—FV×2’°Ð¢Õ÷væD–æfô&"å6WDÆ–æR†—FVÒæf—'7BÂ—FVÒç6V6öæB“°Ð¢ÐÐ Ð¢–b†–æfôFFæ%6†÷t–æfô&"bbÕö6öçG&öÇ2ä6öçG&öÄ6†V6¶VB„4Ö–äg&ÖT6öçG&öÇ3£¥FööÆ&#£¤”ädò’’°Ð¢Õö6öçG&öÇ2åFövvÆT6öçG&öÂ„4Ö–äg&ÖT6öçG&öÇ3£¥FööÆ&#£¤”ädò“°Ð¢ÐÐ¢ÐÐ Ð¢&V6Æ4Æ–÷WB‚“°Ð¢–b†–æfôFFæ%6†÷tõ4B’°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂ46†ææVÄ–æfòÂ3S“°Ð¢ÐÐ Ð¢÷Vå6WGWv–æF÷uF—FÆR‚“°Ð¢ÒVÇ6R°Ð¢54U%B„dÅ4R“°Ð¢ÐÐ Ð¢Õ÷Ed%7FFRÓæ$–æfô7F—fRÒfÇ6S°Ð Ð¢&WGW&â°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WDÆöE7FFR„ÔÅ2U7FFRÐ§°Ð¢–b†U7FFRÓÒÔÅ3£¤ÄôD”ärbbÕöTÖVF–ÆöE7FFRÒÔÅ3£¤4Äõ4TBÇÂU7FFRÓÒÔÅ3£¤d”Ä”ärbbÕöTÖVF–ÆöE7FFRÒÔÅ3£¤ÄôD”är’°Ð¢54U%B†fÇ6R“°Ð¢–b…U4UôÄôttU"„g„vWD6WGF–æw2‚’’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¥6WDÆöE7FFRÒVæW‡V7FVB7FFR6†ævS¢VBÓâVB"’ÂÕöTÖVF–ÆöE7FFRÂU7FFR“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ¢6–bFVf–æVB…ôDT%Tr’bbU4UôE$ETÕô5$4…õ$Uõ%DU"bb„Õ5õdU%4”ôåõ$UbâÐ¢–b„7&6…&W÷'FW#£¤—4Væ&ÆVB‚’’°Ð¢–b„vWD7W'&VçEF‡&VD–B‚’Òg„vWD‚’ÓæÕöåF‡&VD”B’°Ð¢F‡&÷r†FVC°Ð¢ÐÐ¢ÐÐ¢6VæF–`Ð¢ÐÐ Ð¢ÕöTÖVF–ÆöE7FFRÒU7FFS°Ð¢6VæD”æ÷F–g’„4ÔEõ5DDRÂ7FF–5ö67CÆ–çCâ†U7FFR’“°Ð¢–b†U7FFRÓÒÔÅ3£¤ÄôDTB’°Ð¢Õö6öçG&öÇ2äFVÆ•6†÷tæ÷DÆöFVB†fÇ6R“°Ð¢ÕöWfVçF2äf—&TWfVçB„×4WfVçC£¤ÔTD”ôÄôDTB“°Ð¢ÐÐ¢WFFT6öçG&öÅ7FFR…UDDUô4ôåE$ôÅ5õd•4”$”Ä•E’“°Ð§ÐÐ Ð¦–æÆ–æRÔÅ24Ö–äg&ÖS£¤vWDÆöE7FFR‚’6öç7@Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFS°Ð§ÐÐ Ð¦–æÆ–æR&ööÂ4Ö–äg&ÖS£¤—57FFTÆöFVB‚Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDTC°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—57FFTÆöFVD÷$ÆöF–ær‚Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDTBÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôD”äs°Ð§ÐÐ Ð¦–æÆ–æR&ööÂ4Ö–äg&ÖS£¤—57FFT6Æ÷6VB‚Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤4Äõ4TC°Ð§ÐÐ Ð¦–æÆ–æR&ööÂ4Ö–äg&ÖS£¤—57FFT6Æ÷6VD÷$ÆöFVB‚Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤4Äõ4TBÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDTC°Ð§ÐÐ Ð¦–æÆ–æR&ööÂ4Ö–äg&ÖS£¤—57FFT6Æ÷6–æt&÷'F–ær‚Ð§°Ð¢&WGW&âÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤4Äõ4”ärÇÂÕöTÖVF–ÆöE7FFRÓÒÔÅ3£¤$õ%D”äs°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WEÆ•7FFR„Õ5õÄ•5DDR•7FFRÐ§°Ð¢ÕôÆ6Bå6WEÆ•7FFR‚„4Õ5ôÆ6C£¥Æ•7FFR–•7FFR“°Ð¢6VæD”æ÷F–g’„4ÔEõÄ”ÔôDRÂ•7FFR“°Ð Ð¢–b†ÕödVæDöe7G&VÒ’°Ð¢6VæD”6öÖÖæB„4ÔEôäõD”e”TäDôe5E$TÒÂÂ%Ã"“²òòFòæ÷B72åTÄÂ†W&RÐ¢ÐÐ Ð¢–b†•7FFRÓÒ5õÄ’’°Ð¢òò&WfVçB6ÆVWv†VâÆ––ærVF–òæBö÷"f–FVòÂ'WBÆÆ÷r67&VVç6fW"v†VâöæÇ’VF–ðÐ¢–b‚ÕödVF–ôöæÇ’bbg„vWD6WGF–æw2‚’æ%&WfVçDF—7Æ•6ÆVW’°Ð¢6WEF‡&VDW†V7WF–öå7FFR„U5ô4ôåD”åTõU2ÂU5ôD•5Ä•õ$UT•$TBÂU5õ5•5DTÕõ$UT•$TB“°Ð¢ÒVÇ6R°Ð¢6WEF‡&VDW†V7WF–öå7FFR„U5ô4ôåD”åTõU2ÂU5õ5•5DTÕõ$UT•$TB“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢6WEF‡&VDW†V7WF–öå7FFR„U5ô4ôåD”åTõU2“°Ð¢ÐÐ Ð Ð¢WFFUF‡VÖ&$'WGFöâ†•7FFR“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤7&VFTgVÆÅ67&VVåv–æF÷r†&ööÂ—4C4Bò¢ÒG'VR¢òÐ§°Ð¢–b†Õö$gVÆÅ67&VVåv–æF÷t—4C4BÓÒ—4C4Bbb†4FVF–6FVDe5f–FVõv–æF÷r‚’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢4Ööæ—F÷'2Ööæ—F÷'3°Ð¢4Ööæ—F÷"Ööæ—F÷"Â7W'&VçDÖöæ—F÷#°Ð Ð¢–b†Õ÷FVF–6FVDe5f–FVõvæBÓä—5v–æF÷r‚’’°Ð¢Õ÷FVF–6FVDe5f–FVõvæBÓäFW7G&÷•v–æF÷r‚“°Ð¢ÐÐ Ð¢7W'&VçDÖöæ—F÷"ÒÖöæ—F÷'2ävWDæV&W7DÖöæ—F÷"‡F†—2“°Ð¢–b‡2æ”Ööæ—F÷"ÓÒ’°Ð¢Ööæ—F÷"ÒÖöæ—F÷'2ävWDÖöæ—F÷"‡2ç7G$gVÆÅ67&VVäÖöæ—F÷$”BÂ2ç7G$gVÆÅ67&VVäÖöæ—F÷$FWf–6TæÖR“°Ð¢ÐÐ¢–b‚Ööæ—F÷"ä—4Ööæ—F÷"‚’’°Ð¢Ööæ—F÷"Ò7W'&VçDÖöæ—F÷#°Ð¢ÐÐ Ð¢5&V7BÖöæ—F÷%&V7C°Ð¢Ööæ—F÷"ävWDÖöæ—F÷%&V7B†Ööæ—F÷%&V7B“°Ð Ð¢Õö$gVÆÅ67&VVåv–æF÷t—4C4BÒ—4C4C°Ð¢Õö$gVÆÅ67&VVåv–æF÷t—4öå6W&FTF—7Æ’ÒÖöæ—F÷"Ò7W'&VçDÖöæ—F÷#°Ð Ð¢òòÆÆ÷rF†RÖ–æg&ÖRFò¶VWfö7W0Ð¢&ööÂ&WBÒÕ÷FVF–6FVDe5f–FVõvæBÓä7&VFTW‚…u5ôU…õDõÔõ5BÂu5ôU…õDôôÅt”äDõrÂõB‚""’Â&W57G"„”E5ôÔ”äe$Õó3b’Âu5õõUÂÖöæ—F÷%&V7BÂçVÆÇG"Â“°Ð¢–b‡&WB’°Ð¢Õ÷FVF–6FVDe5f–FVõvæBÓå6†÷uv–æF÷r…5uõ4„õtäô5D•dDR“°Ð¢ÐÐ¢&WGW&â&WC°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4g&ÖTÆW75v–æF÷r‚’6öç7@Ð§°Ð¢&WGW&â„—4gVÆÅ67&VVäÖ–äg&ÖR‚’ÇÂg„vWD6WGF–æw2‚’æT6F–öäÖVçTÖöFRÓÒÔôDUô$õ$DU$ÄU52“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—46F–öä†–FFVâ‚’6öç7@Ð§°Ð¢òò–bæò6F–öâÂF†W&R—2æòÖVçR&"â'WB–b—2æòÖVçR&"ÂF†VâF†R6F–öâ6â&RàÐ¢&WGW&â‚—4gVÆÅ67&VVäÖ–äg&ÖR‚’bbg„vWD6WGF–æw2‚’æT6F–öäÖVçTÖöFRâÔôDUô„”DTÔTåR“²òòÔÔôDUõ4„õt4D”ôäÔTåRbbÔÔôDUô„”DTÔTåPÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4ÖVçT†–FFVâ‚’6öç7@Ð§°Ð¢&WGW&â‚—4gVÆÅ67&VVäÖ–äg&ÖR‚’bbg„vWD6WGF–æw2‚’æT6F–öäÖVçTÖöFRÒÔôDUõ4„õt4D”ôäÔTåR“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—5Æ–Æ—7DV×G’‚’6öç7@Ð§°Ð¢&WGW&â†Õ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’ÓÒ“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4–çFW&7F—fUf–FVò‚’6öç7@Ð§°Ð¢&WGW&âÕöe6†ö6·vfTw&ƒ°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4gVÆÅ67&VVäÖöFR‚’6öç7B°Ð¢&WGW&âÕödgVÆÅ67&VVâÇÂ—4C4DgVÆÅ67&VVäÖöFR‚“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4gVÆÅ67&VVäÖ–äg&ÖR‚’6öç7B°Ð¢&WGW&âÕödgVÆÅ67&VVâbb†4FVF–6FVDe5f–FVõv–æF÷r‚“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4gVÆÅ67&VVäÖ–äg&ÖTW†6ÇW6—fTÕ5e"‚’6öç7B°Ð¢&WGW&âÕödgVÆÅ67&VVâbbÕö$—4Õ5e$W†6ÇW6—fTÖöFRbb†4FVF–6FVDe5f–FVõv–æF÷r‚“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4gVÆÅ67&VVå6W&FR‚’6öç7B°Ð¢&WGW&âÕödgVÆÅ67&VVâbb†4FVF–6FVDe5f–FVõv–æF÷r‚’bbÕö$gVÆÅ67&VVåv–æF÷t—4C4C°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤†4FVF–6FVDe5f–FVõv–æF÷r‚’6öç7B°Ð¢&WGW&âÕ÷FVF–6FVDe5f–FVõvæBbbÕ÷FVF–6FVDe5f–FVõvæBÓä—5v–æF÷r‚“°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4C4DgVÆÅ67&VVäÖöFR‚’6öç7@Ð§°Ð¢&WGW&â†4FVF–6FVDe5f–FVõv–æF÷r‚’bbÕö$gVÆÅ67&VVåv–æF÷t—4C4C°Ð§Ó°Ð Ð¦&ööÂ4Ö–äg&ÖS£¤—57V'&W7–æ4&%f—6–&ÆR‚’6öç7@Ð§°Ð¢&WGW&âÕ÷væE7V'&W7–æ4&"ä—5v–æF÷uf—6–&ÆR‚“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WGWUe$6öÆ÷$6öçG&öÂ‚Ð§°Ð¢–b†Õ÷Ôee’°Ð¢4ÕÆ–W$4¢Òg„vWD×”‚“°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b„d”ÄTB†Õ÷ÔeeÓävWE&ö4×&ævR„E…d%õ&ö4×ô'&–v‡FæW72ÂÓävWDUe$6öÆ÷$6öçG&öÂ…&ö4×ô'&–v‡FæW72’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷ÔeeÓävWE&ö4×&ævR„E…d%õ&ö4×ô6öçG&7BÂÓävWDUe$6öÆ÷$6öçG&öÂ…&ö4×ô6öçG&7B’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷ÔeeÓävWE&ö4×&ævR„E…d%õ&ö4×ô‡VRÂÓävWDUe$6öÆ÷$6öçG&öÂ…&ö4×ô‡VR’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷ÔeeÓävWE&ö4×&ævR„E…d%õ&ö4×õ6GW&F–öâÂÓävWDUe$6öÆ÷$6öçG&öÂ…&ö4×õ6GW&F–öâ’’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢ÓåWFFT6öÆ÷$6öçG&öÅ&ævR‡G'VR“°Ð¢6WD6öÆ÷$6öçG&öÂ…&ö4×ôÆÂÂ2æ”'&–v‡FæW72Â2æ”6öçG&7BÂ2æ”‡VRÂ2æ•6GW&F–öâ“°Ð¢ÐÐ§ÐÐ Ð¢òò6ÆÆVBg&öÒw&…F‡&V@Ð§fö–B4Ö–äg&ÖS£¥6WGWdÕ#”6öÆ÷$6öçG&öÂ‚Ð§°Ð¢–b†Õ÷dÕ$Ô2’°Ð¢4ÕÆ–W$4¢Òg„vWD×”‚“°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b„d”ÄTB†Õ÷dÕ$Ô2ÓävWE&ö4×6öçG&öÅ&ævRƒÂÓävWEdÕ#”6öÆ÷$6öçG&öÂ…&ö4×ô'&–v‡FæW72’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷dÕ$Ô2ÓävWE&ö4×6öçG&öÅ&ævRƒÂÓävWEdÕ#”6öÆ÷$6öçG&öÂ…&ö4×ô6öçG&7B’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷dÕ$Ô2ÓävWE&ö4×6öçG&öÅ&ævRƒÂÓävWEdÕ#”6öÆ÷$6öçG&öÂ…&ö4×ô‡VR’’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„d”ÄTB†Õ÷dÕ$Ô2ÓävWE&ö4×6öçG&öÅ&ævRƒÂÓävWEdÕ#”6öÆ÷$6öçG&öÂ…&ö4×õ6GW&F–öâ’’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢ÓåWFFT6öÆ÷$6öçG&öÅ&ævR†fÇ6R“°Ð¢6WD6öÆ÷$6öçG&öÂ…&ö4×ôÆÂÂ2æ”'&–v‡FæW72Â2æ”6öçG&7BÂ2æ”‡VRÂ2æ•6GW&F–öâ“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WD6öÆ÷$6öçG&öÂ„Etõ$BfÆw2Â–çBb'&–v‡FæW72Â–çBb6öçG&7BÂ–çBb‡VRÂ–çBb6GW&F–öâÐ§°Ð¢4ÕÆ–W$4¢Òg„vWD×”‚“°Ð¢…$U5TÅB‡"Ò°Ð Ð¢7FF–2dÕ#•&ö4×6öçG&öÂ6Ç$6öçG&öÃ°Ð¢7FF–2E…d%õ&ö4×fÇVW26Ç%fÇVW3°Ð Ð¢4ôÄõ%$õU%E•õ$ätR¢7"Ò°Ð¢–b†fÆw2b&ö4×ô'&–v‡FæW72’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×ô'&–v‡FæW72“°Ð¢'&–v‡FæW72Ò7FC£¦Ö–â‡7FC£¦Ö‚†'&–v‡FæW72Â7"ÓäÖ–åfÇVR’Â7"ÓäÖ…fÇVR“°Ð¢ÐÐ¢–b†fÆw2b&ö4×ô6öçG&7B’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×ô6öçG&7B“°Ð¢6öçG&7BÒ7FC£¦Ö–â‡7FC£¦Ö‚†6öçG&7BÂ7"ÓäÖ–åfÇVR’Â7"ÓäÖ…fÇVR“°Ð¢ÐÐ¢–b†fÆw2b&ö4×ô‡VR’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×ô‡VR“°Ð¢‡VRÒ7FC£¦Ö–â‡7FC£¦Ö‚†‡VRÂ7"ÓäÖ–åfÇVR’Â7"ÓäÖ…fÇVR“°Ð¢ÐÐ¢–b†fÆw2b&ö4×õ6GW&F–öâ’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×õ6GW&F–öâ“°Ð¢6GW&F–öâÒ7FC£¦Ö–â‡7FC£¦Ö‚‡6GW&F–öâÂ7"ÓäÖ–åfÇVR’Â7"ÓäÖ…fÇVR“°Ð¢ÐÐ Ð¢–b†Õ÷dÕ$Ô2’°Ð¢6Ç$6öçG&öÂæGu6—¦RÒ6—¦Vöb„6Ç$6öçG&öÂ“°Ð¢6Ç$6öçG&öÂæGtfÆw2ÒfÆw3°Ð¢6Ç$6öçG&öÂä'&–v‡FæW72Ò†fÆöB–'&–v‡FæW73°Ð¢6Ç$6öçG&öÂä6öçG&7BÒ†fÆöB’†6öçG&7B²’ò°Ð¢6Ç$6öçG&öÂä‡VRÒ†fÆöB–‡VS°Ð¢6Ç$6öçG&öÂå6GW&F–öâÒ†fÆöB’‡6GW&F–öâ²’ò°Ð Ð¢‡"ÒÕ÷dÕ$Ô2Óå6WE&ö4×6öçG&öÂƒÂd6Ç$6öçG&öÂ“°Ð¢ÒVÇ6R–b†Õ÷Ôee’°Ð¢6Ç%fÇVW2ä'&–v‡FæW72Ò–çEFôf—†VB†'&–v‡FæW72“°Ð¢6Ç%fÇVW2ä6öçG&7BÒ–çEFôf—†VB†6öçG&7B²Â“°Ð¢6Ç%fÇVW2ä‡VRÒ–çEFôf—†VB†‡VR“°Ð¢6Ç%fÇVW2å6GW&F–öâÒ–çEFôf—†VB‡6GW&F–öâ²Â“°Ð Ð¢‡"ÒÕ÷ÔeeÓå6WE&ö4×fÇVW2†fÆw2Âd6Ç%fÇVW2“°Ð Ð¢ÐÐ¢òòv÷&¶&÷VæC¢v—F‚–çFVÂG&—fW"F†RÖ–æ–×VÒfÇVW2öbF†R7W÷'FVB&ævRÖ’æ÷B7GVÆÇ’v÷&°Ð¢–b„d”ÄTB†‡"’’°Ð¢–b†fÆw2b&ö4×ô'&–v‡FæW72’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×ô'&–v‡FæW72“°Ð¢–b†'&–v‡FæW72ÓÒ7"ÓäÖ–åfÇVR’°Ð¢'&–v‡FæW72Ò7"ÓäÖ–åfÇVR²°Ð¢ÐÐ¢ÐÐ¢–b†fÆw2b&ö4×ô‡VR’°Ð¢7"ÒÓävWD6öÆ÷$6öçG&öÂ…&ö4×ô‡VR“°Ð¢–b†‡VRÓÒ7"ÓäÖ–åfÇVR’°Ð¢‡VRÒ7"ÓäÖ–åfÇVR²°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6WD6Æ÷6VD6F–öç2†&ööÂVæ&ÆRÐ§°Ð¢–b†Õ÷Äã#’°Ð¢Õ÷Äã#Óå6WE6W'f–6U7FFR†Væ&ÆRòÕôÃ#ô455DDUôöâ¢ÕôÃ#ô455DDUôöfb“°Ð¢ÐÐ§ÐÐ Ð¤Å5E5E"4Ö–äg&ÖS£¤vWDEdDVF–ôf÷&ÖDæÖR†6öç7BEdEôVF–ôGG&–'WFW2bE"’6öç7@Ð§°Ð¢7v—F6‚„E"äVF–ôf÷&ÖB’°Ð¢66REdEôVF–ôf÷&ÖEô33 Ð¢&WGW&âõB‚$32"“°Ð¢66REdEôVF–ôf÷&ÖEôÕTs Ð¢66REdEôVF–ôf÷&ÖEôÕTsôE$3 Ð¢&WGW&âõB‚$ÕTs"“°Ð¢66REdEôVF–ôf÷&ÖEôÕTs# Ð¢66REdEôVF–ôf÷&ÖEôÕTs%ôE$3 Ð¢&WGW&âõB‚$ÕTs""“°Ð¢66REdEôVF–ôf÷&ÖEôÅ4Ó Ð¢&WGW&âõB‚$Å4Ò"“°Ð¢66REdEôVF–ôf÷&ÖEôEE3 Ð¢&WGW&âõB‚$EE2"“°Ð¢66REdEôVF–ôf÷&ÖEõ4DE3 Ð¢&WGW&âõB‚%4DE2"“°Ð¢66REdEôVF–ôf÷&ÖEô÷F†W# Ð¢FVfVÇC Ð¢&WGW&âÔ´T”åE$U4õU$4R„”E5ôÔ”äe$Õó3r“°Ð¢ÐÐ§ÐÐ Ð¦g…ö×6rfö–B4Ö–äg&ÖS£¤öäv÷Fõ7V'F—FÆR…T”åBä”BÐ§°Ð¢–b‚Õ÷7V%7G&V×2ä—4V×G’‚’bb—5Æ–&6´6GW&TÖöFR‚’’°Ð¢Õ÷'D7W%7V%÷2ÒÕ÷væE6VV´&"ävWE÷2‚“°Ð¢ÕöÅ7V'F—FÆU6†–gBÒ°Ð¢Õ÷væE7V'&W7–æ4&"å&Vg&W6„VÖ&VFFVEFW‡E7V'F—FÆTFF‚“°Ð¢Õöä7W%7V'F—FÆRÒÕ÷væE7V'&W7–æ4&"äf–æDæV&W7E7V"†Õ÷'D7W%7V%÷2Â†ä”BÓÒ”EôtõDõôäU…Eõ5T"’“°Ð¢–b†Õöä7W%7V'F—FÆRãÒbbÕ÷Õ2’°Ð¢–b†ä”BÓÒ”EôtõDõõ$Ueõ5T"’°Ð¢öåÆ•W6R‚“°Ð¢ÐÐ¢Õ÷Õ2Óå6WE÷6—F–öç2‚fÕ÷'D7W%7V%÷2ÂÕõ4TT´”äuô'6öÇWFU÷6—F–öæ–ærÂçVÆÇG"ÂÕõ4TT´”äuôæõ÷6—F–öæ–ær“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦g…ö×6rfö–B4Ö–äg&ÖS£¤öå7V'&W7–æ56†–gE7V"…T”åBä”BÐ§°Ð¢–b†Õöä7W%7V'F—FÆRãÒ’°Ð¢ÆöærÅ6†–gBÒ†ä”BÓÒ”Eõ5T%$U5”ä5õ4„”eEôDõtâ’òÓ¢°Ð¢57G&–ær7G%7V%6†–gC°Ð Ð¢–b†Õ÷væE7V'&W7–æ4&"å6†–gE7V'F—FÆR†Õöä7W%7V'F—FÆRÂÅ6†–gBÂÕ÷'D7W%7V%÷2’’°Ð¢ÕöÅ7V'F—FÆU6†–gB³ÒÅ6†–gC°Ð¢–b†Õ÷Õ2’°Ð¢Õ÷Õ2Óå6WE÷6—F–öç2‚fÕ÷'D7W%7V%÷2ÂÕõ4TT´”äuô'6öÇWFU÷6—F–öæ–ærÂçVÆÇG"ÂÕõ4TT´”äuôæõ÷6—F–öæ–ær“°Ð¢ÐÐ¢ÐÐ Ð¢7G%7V%6†–gBäf÷&ÖB„”E5ôÔ”äe$Õó3‚ÂÕöÅ7V'F—FÆU6†–gB“°Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂ7G%7V%6†–gB“°Ð¢ÐÐ§ÐÐ Ð¦g…ö×6rfö–B4Ö–äg&ÖS£¤öå7V'F—FÆTFVÆ’…T”åBä”BÐ§°Ð¢–çBäFVÆ•7FWÒg„vWD6WGF–æw2‚’æå7V$FVÆ•7FW°Ð Ð¢–b†ä”BÓÒ”Eõ5T%ôDTÄ•ôDõtâ’°Ð¢äFVÆ•7FWÒÖäFVÆ•7FW°Ð¢ÐÐ Ð¢6WE7V'F—FÆTFVÆ’†äFVÆ•7FWÂò§&VÆF—fSÒ¢òG'VR“°Ð§ÐÐ Ð¦g…ö×6rfö–B4Ö–äg&ÖS£¤öå7V'F—FÆU÷2…T”åBä”BÐ§°Ð¢–b†Õ÷4’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢7v—F6‚†ä”B’°Ð¢66R”Eõ5T%õõ5ôDõtã Ð¢2æÕõ&VæFW&W'56WGF–æw2ç7V%–5fW'F–6Å6†–gB³Ò#°Ð¢'&V³°Ð¢66R”Eõ5T%õõ5õU Ð¢2æÕõ&VæFW&W'56WGF–æw2ç7V%–5fW'F–6Å6†–gBÓÒ#°Ð¢'&V³°Ð¢ÐÐ Ð¢–b„vWDÖVF–7FFR‚’Ò7FFUõ'Vææ–ær’°Ð¢Õ÷4Óå–çB†fÇ6R“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦g…ö×6rfö–B4Ö–äg&ÖS£¤öå7V'F—FÆTföçE6—¦R…T”åBä”BÐ§°Ð¢–b†Õ÷4bbÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢4Å4”B6Ç6–C°Ð¢Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÓävWD6Æ74”B‚f6Ç6–B“°Ð¢–b†6Ç6–BÓÒõ÷WV–Föb„5&VæFW&VEFW‡E7V'F—FÆR’’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢7v—F6‚†ä”B’°Ð¢66R”Eõ5T%ôdôåEõ4•¤UôDT3 Ð¢2æÕõ&VæFW&W'56WGF–æw2æföçE66ÆT÷fW'&–FRÓÒãS°Ð¢'&V³°Ð¢66R”Eõ5T%ôdôåEõ4•¤Uô”ä3 Ð¢2æÕõ&VæFW&W'56WGF–æw2æföçE66ÆT÷fW'&–FR³ÒãS°Ð¢'&V³°Ð¢ÐÐ Ð¢5&VæFW&VEFW‡E7V'F—FÆR¢%E2Ò„5&VæFW&VEFW‡E7V'F—FÆR¢’„•7V%7G&VÒ¢–Õ÷7W'&VçE7V$–çWBç7V%7G&VÓ°Ð Ð¢–b‡%E2ÓæÕôÆ–&746öçFW‡Bä—4Æ–&747F—fR‚’’°Ð¢òòæ÷B7W÷'FVB'’Æ–&72‡–WBÐ¢–b‚—4gVÆÅ67&VVäÖöFR‚’’°Ð¢g„ÖW76vT&÷‚…õB‚$F§W7F–ær7V'F—FÆRFW‡B6—¦R—2æ÷B÷76–&ÆRv†VâW6–ærÆ–&72â"’ÂÔ%ô”4ôäU%$õ"Â“°Ð¢ÐÐ¢ÐÐ Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢%E2ÓäFV–æ—B‚“°Ð¢ÐÐ¢–çfÆ–FFU7V'F—FÆR‚“°Ð Ð¢–b„vWDÖVF–7FFR‚’Ò7FFUõ'Vææ–ær’°Ð¢Õ÷4Óå–çB†fÇ6R“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b‚—4gVÆÅ67&VVäÖöFR‚’’°Ð¢g„ÖW76vT&÷‚…õB‚$F§W7F–ær7V'F—FÆRFW‡B6—¦R—2æ÷B÷76–&ÆRf÷"–ÖvR&6VB7V'F—FÆRf÷&ÖG2â"’ÂÔ%ô”4ôäU%$õ"Â“°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&W6WE7V'F—FÆU÷4æE6—¦R†&ööÂ&W–çBò¢ÒfÇ6R¢òÐ§°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢&ööÂ6†ævVBÒ‡2æÕõ&VæFW&W'56WGF–æw2æföçE66ÆT÷fW'&–FRÒã’ÇÂ‡2æÕõ&VæFW&W'56WGF–æw2ç7V%–5fW'F–6Å6†–gBÒ“°Ð Ð¢2æÕõ&VæFW&W'56WGF–æw2æföçE66ÆT÷fW'&–FRÒã°Ð¢2æÕõ&VæFW&W'56WGF–æw2ç7V%–5fW'F–6Å6†–gBÒ°Ð Ð¢–b†6†ævVBbb&W–çBbbÕ÷4bbÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢4Å4”B6Ç6–C°Ð¢Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÓävWD6Æ74”B‚f6Ç6–B“°Ð¢–b†6Ç6–BÓÒõ÷WV–Föb„5&VæFW&VEFW‡E7V'F—FÆR’’°Ð¢5&VæFW&VEFW‡E7V'F—FÆR¢%E2Ò„5&VæFW&VEFW‡E7V'F—FÆR¢’„•7V%7G&VÒ¢–Õ÷7W'&VçE7V$–çWBç7V%7G&VÓ°Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢%E2ÓäFV–æ—B‚“°Ð¢ÐÐ¢–çfÆ–FFU7V'F—FÆR‚“°Ð Ð¢–b„vWDÖVF–7FFR‚’Ò7FFUõ'Vææ–ær’°Ð¢Õ÷4Óå–çB†fÇ6R“°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð Ð§7FF–2&ööÂ'6T•7FGW4ÖW76vR†6öç7B4õ”DD5E%T5B¢4E2Â57G&–æurbÖW76vRÐ§°Ð¢6öç7FW‡"6—¦U÷BÖ„6öFUVæ—G2ÒS#°Ð¢–b‚4E2ÇÂ4E2ÓæÇFFÇÂ4E2Óæ6$FFÂ"¢6—¦Vöb‡v6†%÷BÐ¢ÇÂ4E2Óæ6$FFâ†Ö„6öFUVæ—G2²’¢6—¦Vöb‡v6†%÷BÐ¢ÇÂ4E2Óæ6$FFR6—¦Vöb‡v6†%÷B’Ò’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢6öç7Bv6†%÷B¢6öç7BfÇVRÒ7FF–5ö67CÆ6öç7Bv6†%÷B£â‡4E2ÓæÇFF“°Ð¢6öç7B6—¦U÷B6öFUVæ—G2Ò4E2Óæ6$FFò6—¦Vöb‡v6†%÷B’Ò°Ð¢–b‡fÇVU¶6öFUVæ—G5ÒÒÂuÃrÇÂvÖVÖ6‡"‡fÇVRÂÂuÃrÂ6öFUVæ—G2’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢f÷"‡6—¦U÷B’Ò²’Â6öFUVæ—G3²’²²’°Ð¢6öç7Bv6†%÷B6öFUVæ—BÒfÇVU¶•Ó°Ð¢–b†6öFUVæ—BãÒ„Cƒbb6öFUVæ—BÃÒ„D$db’°Ð¢–b‚²¶’ãÒ6öFUVæ—G2ÇÂfÇVU¶•ÒÂ„D3ÇÂfÇVU¶•Òâ„Dddb’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÒVÇ6R–b‚†6öFUVæ—BãÒ„D3bb6öFUVæ—BÃÒ„DddbÐ¢ÇÂ6öFUVæ—BÂƒ# Ð¢ÇÂ†6öFUVæ—BãÒƒtbbb6öFUVæ—BÃÒƒ”bÐ¢ÇÂ6öFUVæ—BÓÒƒ##‚ÇÂ6öFUVæ—BÓÒƒ##’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ Ð¢ÖW76vRå6WE7G&–ær‡fÇVRÂ7FF–5ö67CÆ–çCâ†6öFUVæ—G2’“°Ð¢&WGW&âG'VS°Ð§ÐÐ Ð§7FF–2&ööÂ'6T”–çFVvW"†6öç7B4õ”DD5E%T5B¢4E2Â–çBÖ–æ–×VÒÂ–çBÖ†–×VÒÂ–çBb&W7VÇBÐ§°Ð¢–b‚4E2ÇÂ4E2ÓæÇFFÇÂ4E2Óæ6$FFÂ6—¦Vöb‡v6†%÷BÐ¢ÇÂ4E2Óæ6$FFR6—¦Vöb‡v6†%÷B’Ò’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢6öç7Bv6†%÷B¢6öç7BfÇVRÒ7FF–5ö67CÆ6öç7Bv6†%÷B£â‡4E2ÓæÇFF“°Ð¢6öç7B6—¦U÷BÆVæwF‚Ò4E2Óæ6$FFò6—¦Vöb‡v6†%÷B“°Ð¢–b†ÆVæwF‚âBÇÂfÇVU¶ÆVæwF‚ÒÒÒÂuÃpÐ¢ÇÂvÖVÖ6‡"‡fÇVRÂÂuÃrÂÆVæwF‚ÒÐ¢ÇÂfÇVU³ÒÂÂsrÇÂfÇVU³ÒâÂs’r’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢v6†%÷B¢VæBÒçVÆÇG#°Ð¢6öç7BÆöær'6VBÒv77FöÂ‡fÇVRÂfVæBÂ“°Ð¢–b†VæBÓÒfÇVRÇÂ¦VæBÒÂuÃrÇÂ'6VBÂÖ–æ–×VÒÇÂ'6VBâÖ†–×VÒ’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢&W7VÇBÒ7FF–5ö67CÆ–çCâ‡'6VB“°Ð¢&WGW&âG'VS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&ö6W74”6öÖÖæB„…täB…6VæFW"Â4õ”DD5E%T5B¢4E2Ð§°Ð¢4FÄÆ—7CÄ57G&–æsâfç3°Ð¢$TdU$Tä4UõD”ÔR'E÷2Ò°Ð¢57G&–ærfã°Ð Ð¢–b…U4UôÄôttU"„g„vWD6WGF–æw2‚’’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¥&ö6W74”6öÖÖæBÒ4ÔCÒVÇR"’Â4E2ÓæGtFF“°Ð¢ÐÐ Ð¢7v—F6‚‡4E2ÓæGtFF’°Ð¢66R4ÔEôõTäd”ÄS Ð¢fâÒ57G&–ær‚„Å5u5E"—4E2ÓæÇFF“°Ð¢–b„vWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅW6R‡G'VR“°Ð¢ÐÐ¢–b„6å6VæEFõ–÷WGV&TDÂ†fâ’’°Ð¢–b…&ö6W75–÷WGV&TDÅU$Â†fâÂfÇ6R’’°Ð¢÷7DÖW76vR…tÕôÕ5ôõTä5U%Ä”Ä•5BÂÂ“°Ð¢&WGW&ã°Ð¢ÒVÇ6R–b„—4öå”DÅv†—FVÆ—7B†fâ’’°Ð¢Õö6Æ÷6–æv×6rÒÂ$f–ÆVBFòW‡G&7B7G&VÒU$Âv—F‚—BÖFÇ÷–÷WGV&RÖFÂ#°Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR†Õö6Æ÷6–æv×6r“°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ¢fç2äFD†VB†fâ“°Ð¢Õ÷væEÆ–Æ—7D&"ä÷Vâ†fç2ÂfÇ6R“°Ð¢÷7DÖW76vR…tÕôÕ5ôõTä5U%Ä”Ä•5BÂÂ“°Ð¢'&V³°Ð¢66R4ÔEõ5Dõ Ð¢öåÆ•7F÷‚“°Ð¢'&V³°Ð¢66R4ÔEô4Äõ4Td”ÄS Ð¢÷7DÖW76vR…tÕô4ôÔÔäBÂ”Eôd”ÄUô4Äõ4TÔTD”“°Ð¢'&V³°Ð¢66R4ÔEõÄ•U4S Ð¢öåÆ•Æ—W6R‚“°Ð¢'&V³°Ð¢66R4ÔEõÄ“ Ð¢öä•Æ’‚“°Ð¢'&V³°Ð¢66R4ÔEõU4S Ð¢öä•W6R‚“°Ð¢'&V³°Ð¢66R4ÔEôDEDõÄ”Ä•5C Ð¢fâÒ57G&–ær‚„Å5u5E"—4E2ÓæÇFF“°Ð¢–b„6å6VæEFõ–÷WGV&TDÂ†fâ’’°Ð¢–b…&ö6W75–÷WGV&TDÅU$Â†fâÂG'VR’’°Ð¢&WGW&ã°Ð¢ÒVÇ6R–b„—4öå”DÅv†—FVÆ—7B†fâ’’°Ð¢Õö6Æ÷6–æv×6rÒÂ$f–ÆVBFòW‡G&7B7G&VÒU$Âv—F‚—BÖFÇ÷–÷WGV&RÖFÂ#°Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR†Õö6Æ÷6–æv×6r“°Ð¢&WGW&ã°Ð¢ÐÐ¢ÐÐ¢fç2äFD†VB†fâ“°Ð¢Õ÷væEÆ–Æ—7D&"äVæB†fç2ÂG'VR“°Ð¢'&V³°Ð¢66R4ÔEõ5D%EÄ”Ä•5C Ð¢–b„vWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅW6R‡G'VR“°Ð¢ÐÐ¢÷7DÖW76vR…tÕôÕ5ôõTä5U%Ä”Ä•5BÂÂ“°Ð¢'&V³°Ð¢66R4ÔEô4ÄT%Ä”Ä•5C Ð¢Õ÷væEÆ–Æ—7D&"äV×G’‚“°Ð¢'&V³°Ð¢66R4ÔEõ4UEõ4•D”ôã Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢'E÷2Ò¢$TdU$Tä4UõD”ÔR…÷wFöb‚„Å5u5E"—4E2ÓæÇFF’¢“²ò÷v—F‚67W&7’öb×0Ð¢òò–Ö–ç£¢V–6²æBF—'G’G&–6°Ð¢òòW6RÓå6VVµFòÓåÆ’†–âÆ6Röb6VVµFòöæÇ’’6VV×2Fò&WfVçG2–âÖ÷7B66W0Ð¢òò6öÖR7G&ævRf–FVòVffV7G2öâf’f–ÆW2†W‚âÆö6·2v†–ÆRæBF†â'Vææ–ærf7B’àÐ¢–b‚ÕödVF–ôöæÇ’bbvWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–6öçG&öÅW6R‡G'VR“°Ð¢6VVµFò‡'E÷2“°Ð¢ÖVF–6öçG&öÅ'Vâ‡G'VR“°Ð¢ÒVÇ6R°Ð¢6VVµFò‡'E÷2“°Ð¢ÐÐ¢òò6†÷r7W'&VçB÷6—F–öâ÷fW'&–FFVâ'’Æ’6öÖÖæ@Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂÕ÷væE7FGW4&"ävWE7FGW5F–ÖW"‚’Â#“°Ð¢ÐÐ¢'&V³°Ð¢66R4ÔEõ4UEdôÅTÔS¢°Ð¢–çBföÇVÖS°Ð¢–b†…6VæFW"ÓÒg„vWD6WGF–æw2‚’æ„Ö7FW%væ@Ð¢bb'6T”–çFVvW"‡4E2ÂÂÂföÇVÖR’bbföÇVÖRÒvWEföÇVÖR‚’’°Ð¢òò6WEföÇVÖR÷7G2F†R6æöæ–6ÂföÇVÖRÖ6†ævRæ÷F–f–6F–öâàÐ¢Õ÷væEFööÄ&"å6WEföÇVÖR‡föÇVÖR“°Ð¢ÐÐ¢'&V³°Ð¢ÐÐ¢66R4ÔEõ4UDÕUDS¢°Ð¢–çB×WFS°Ð¢–b†…6VæFW"ÓÒg„vWD6WGF–æw2‚’æ„Ö7FW%væ@Ð¢bb'6T”–çFVvW"‡4E2ÂÂÂ×WFR’bb†×WFRÒ’Ò—4×WFVB‚’’°Ð¢Õ÷væEFööÄ&"å6WD×WFR†×WFRÒ“°Ð¢öåÆ•föÇVÖR„”EõdôÅTÔUôÕUDR“°Ð¢ÐÐ¢'&V³°Ð¢ÐÐ¢66R4ÔEõ4UDTD”ôDTÄ“ Ð¢'E÷2Ò…$TdU$Tä4UõD”ÔR•÷wFöÂ‚„Å5u5E"—4E2ÓæÇFF’¢°Ð¢6WDVF–ôFVÆ’‡'E÷2“°Ð¢'&V³°Ð¢66R4ÔEõ4UE5T%D•DÄTDTÄ“ Ð¢6WE7V'F—FÆTFVÆ’…÷wFö’‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEõ4UD”äDU…Ä”Ä•5C Ð¢òöÕ÷væEÆ–Æ—7D&"å6WE6VÄ–G‚…÷wFö’‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEõ4UDTD”õE$4³ Ð¢6WDVF–õG&6´–G‚…÷wFö’‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEõ4UE5T%D•DÄUE$4³ Ð¢6WE7V'F—FÆUG&6´–G‚…÷wFö’‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEôtUEdU%4”ôã¢°Ð¢57G&–æur'VfbÒg„vWD×”‚’ÓæÕ÷7G%fW'6–öã°Ð¢6VæD”6öÖÖæB„4ÔEõdU%4”ôâÂ'Vfb“°Ð¢'&V³°Ð¢ÐÐ¢66R4ÔEôtUE5T%D•DÄUE$4µ3 Ð¢6VæE7V'F—FÆUG&6·5Fô’‚“°Ð¢'&V³°Ð¢66R4ÔEôtUDTD”õE$4µ3 Ð¢6VæDVF–õG&6·5Fô’‚“°Ð¢'&V³°Ð¢66R4ÔEôtUD5U%$TåDTD”õE$4³ Ð¢6VæD”æ÷F–g’„4ÔEô5U%$TåDTD”õE$4²ÂvWD7W'&VçDVF–õG&6´–G‚‚’“°Ð¢'&V³°Ð¢66R4ÔEôtUD5U%$TåE5T%D•DÄUE$4³ Ð¢6VæD”æ÷F–g’„4ÔEô5U%$TåE5T%D•DÄUE$4²ÂvWD7W'&VçE7V'F—FÆUG&6´–G‚‚’“°Ð¢'&V³°Ð¢66R4ÔEôtUD5U%$TåEõ4•D”ôã Ð¢6VæD7W'&VçE÷6—F–öåFô’‚“°Ð¢'&V³°Ð¢66R4ÔEôtUEdôÅTÔS Ð¢6VæD7W'&VçEföÇVÖUFô’‡G'VR“°Ð¢'&V³°Ð¢66R4ÔEôtUDÕUDS Ð¢6VæD7W'&VçD×WFUFô’‡G'VR“°Ð¢'&V³°Ð¢66R4ÔEôtUDäõuÄ””äs Ð¢6VæDæ÷uÆ––æuFô’‚“°Ð¢'&V³°Ð¢66R4ÔEô¥TÕôdå4T4ôäE3 Ð¢§V×ödå6V6öæG2…÷wFö’‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEôtUEÄ”Ä•5C Ð¢6VæEÆ–Æ—7EFô’‚“°Ð¢'&V³°Ð¢66R4ÔEô¥TÕdõ%t$DÔTC Ð¢öåÆ•6VV²„”EõÄ•õ4TT´dõ%t$DÔTB“°Ð¢'&V³°Ð¢66R4ÔEô¥TÕ$4µt$DÔTC Ð¢öåÆ•6VV²„”EõÄ•õ4TT´$4µt$DÔTB“°Ð¢'&V³°Ð¢66R4ÔEõDôttÄTeTÄÅ45$TTã Ð¢öåf–WtgVÆÇ67&VVâ‚“°Ð¢'&V³°Ð¢66R4ÔEô”ä5$T4UdôÅTÔS Ð¢Õ÷væEFööÄ&"æÕ÷föÆ7G&Âä–æ7&V6UföÇVÖR‚“°Ð¢'&V³°Ð¢66R4ÔEôDT5$T4UdôÅTÔS Ð¢Õ÷væEFööÄ&"æÕ÷föÆ7G&ÂäFV7&V6UföÇVÖR‚“°Ð¢'&V³°Ð –66R4ÔEõ4„DU%õDôttÄR Ð ”öå6†FW%FövvÆS‚“°Ð –'&V³°Ð¢66R4ÔEô4Äõ4T Ð¢÷7DÖW76vR…tÕô4Äõ4R“°Ð¢'&V³°Ð¢66R4ÔEõ4UE5TTC Ð¢6WEÆ––æu&FR…÷wFöb‚„Å5u5E"—4E2ÓæÇFF’“°Ð¢'&V³°Ð¢66R4ÔEõ4UEå44ã Ð¢g„vWD6WGF–æw2‚’ç7G%å5&W6WBÒ„Å5u5E"—4E2ÓæÇFF°Ð¢Ç•äå66å&W6WE7G&–ær‚“°Ð¢'&V³°Ð¢66R4ÔEôõ4E4„õtÔU54tS Ð¢–b‡4E2ÓæÇFFbb4E2Óæ6$FFãÒ6—¦Vöb„Õ5ôõ4DDD’’°Ð¢6†÷tõ4D7W7FöÔÖW76vT’‚„Õ5ôõ4DDD¢—4E2ÓæÇFF“°Ð¢ÐÐ¢'&V³°Ð¢66R4ÔEõ5DEU54„õtÔU54tS¢°Ð¢57G&–æurÖW76vS°Ð¢6öç7B46WGF–æw2b6WGF–æw2Òg„vWD6WGF–æw2‚“°Ð¢–b†…6VæFW"ÓÒ6WGF–æw2æ„Ö7FW%væBbb—5v–æF÷r†…6VæFW"Ð¢bb'6T•7FGW4ÖW76vR‡4E2ÂÖW76vR’’°Ð¢6VæE7FGW4ÖW76vR†ÖW76vRÂ3ÂG'VRÂG'VR“°Ð¢ÐÐ¢'&V³°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥6VæD•7G&–æuFò„…täB…F&vWBÂÕ4•ô4ôÔÔäBä6öÖÖæBÂ6öç7B57G&–æurb–ÆöBÐ§°Ð¢4õ”DD5E%T5BFFÒ·Ó°Ð¢FFæ6$FFÒ7FF–5ö67CÄEtõ$Câ‚‡–ÆöBävWDÆVæwF‚‚’²’¢6—¦Vöb‡v6†%÷B’“°Ð¢FFæGtFFÒä6öÖÖæC°Ð¢FFæÇFFÒ6öç7Eö67CÇv6†%÷B£â‡–ÆöBävWE7G&–ær‚’“°Ð Ð¢Etõ$EõE"&W7VÇBÒ°Ð¢&WGW&â6VæDÖW76vUF–ÖV÷WB†…F&vWBÂtÕô4õ”DDÂ&V–çFW'&WEö67CÅu$Óâ„vWE6fT‡væB‚’’ÀÐ¢&V–çFW'&WEö67CÄÅ$Óâ‚fFF’ÀÐ¢òòf—&RÖæBÖf÷&vWC²F†RF–ÖV÷WB¶VW26Æ÷rF&vWBg&öÒ7FÆÆ–ær÷W"TÐ¢òòF‡&VBÂ'WB—2vVæW&÷W2Væ÷Vv‚F†BÖW&VÇ’'W7’F&vWB7F–ÆÂvWG2—@Ð¢4ÕDõô$õ%D”d…TärÂ4ÕDõôU%$õ$ôäU„•BÂSÂg&W7VÇB’Ò°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæD”6öÖÖæB„Õ4•ô4ôÔÔäBä6öÖÖæBÂÅ5u5E"f×BÂâââÐ§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b‡2æ„Ö7FW%væB’°Ð¢4õ”DD5E%T5B4E3°Ð Ð¢föÆ—7B&w3°Ð¢f÷7F'B†&w2Âf×B“°Ð Ð¢–çBä'VffW$ÆVâÒ÷g67G&–çFb†f×BÂ&w2’²²òò÷g67G&–çFbFöW6âwB6÷VçBF†RçVÆÂFW&Ö–æF÷ Ð¢D4„"¢'VfbÒDT%TuôäUrD4„%¶ä'VffW$ÆVåÓ°Ð¢÷g7G&–çFe÷2‡'VfbÂä'VffW$ÆVâÂf×BÂ&w2“°Ð Ð¢4E2æ6$FFÒ„Etõ$B–ä'VffW$ÆVâ¢6—¦Vöb…D4„"“°Ð¢4E2æGtFFÒä6öÖÖæC°Ð¢4E2æÇFFÒ„Ådô”B—'Vfc°Ð Ð¢£¥6VæDÖW76vR‡2æ„Ö7FW%væBÂtÕô4õ”DDÂ…u$Ò”vWE6fT‡væB‚’Â„Å$Ò’d4E2“°Ð Ð¢föVæB†&w2“°Ð¢FVÆWFRµÒ'Vfc°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæDæ÷uÆ––æuFô’†&ööÂ6VæGG&6¶–æfòÐ§°Ð¢–b‚g„vWD6WGF–æw2‚’æ„Ö7FW%væB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢57G&–ærF—FÆRÂWF†÷"ÂFW67&—F–öã°Ð¢57G&–ærÆ&VÃ°Ð¢57G&–ær7G$GW#°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢Õ÷væD–æfô&"ävWDÆ–æR…7G%&W2„”E5ô”ädô$%õD•DÄR’ÂF—FÆR“°Ð¢Õ÷væD–æfô&"ävWDÆ–æR…7G%&W2„”E5ô”ädô$%ôUD„õ"’ÂWF†÷"“°Ð¢Õ÷væD–æfô&"ävWDÆ–æR…7G%&W2„”E5ô”ädô$%ôDU45$•D”ôâ’ÂFW67&—F–öâ“°Ð Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’’°Ð¢Æ&VÂÒÆ’æÕöÆ&VÂä—4V×G’‚’òÆ’æÕöÆ&VÂ¢Æ’æÕöfç2ävWD†VB‚“°Ð¢$TdU$Tä4UõD”ÔR'DGW#°Ð¢Õ÷Õ2ÓävWDGW&F–öâ‚g'DGW"“°Ð¢7G$GW"äf÷&ÖB„Â"Rã6b"Â'DGW"òã“°Ð¢ÐÐ¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢EdEôDôÔ”âEdDFöÖ–ã°Ð¢TÄôärVÄçVÔöd6†FW'2Ò°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö6F–öã°Ð Ð¢òòvWB7W'&VçBEdBFöÖ–àÐ¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDFöÖ–â‚dEdDFöÖ–â’’’°Ð¢7v—F6‚„EdDFöÖ–â’°Ð¢66REdEôDôÔ”åõ7F÷ Ð¢F—FÆRÒõB‚$EdBÒ7F÷VB"“°Ð¢'&V³°Ð¢66REdEôDôÔ”åôf—'7EÆ“ Ð¢F—FÆRÒõB‚$EdBÒf—'7EÆ’"“°Ð¢'&V³°Ð¢66REdEôDôÔ”åõf–FVôÖævW$ÖVçS Ð¢F—FÆRÒõB‚$EdBÒ&ö÷DÖVçR"“°Ð¢'&V³°Ð¢66REdEôDôÔ”åõf–FVõF—FÆU6WDÖVçS Ð¢F—FÆRÒõB‚$EdBÒF—FÆTÖVçR"“°Ð¢'&V³°Ð¢66REdEôDôÔ”åõF—FÆS Ð¢F—FÆRÒõB‚$EdBÒF—FÆR"“°Ð¢'&V³°Ð¢ÐÐ Ð¢òòvWBF—FÆR–æf÷&ÖF–öàÐ¢–b„EdDFöÖ–âÓÒEdEôDôÔ”åõF—FÆR’°Ð¢òòvWB7W'&VçBÆö6F–öâ‡F—FÆRçVÖ&W"b6†FW"Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚dÆö6F–öâ’’’°Ð¢òòvWBçVÖ&W"öb6†FW'2–â7W'&VçBF—FÆPÐ¢dU$”e’…5T44TTDTB†Õ÷EdD’ÓävWDçVÖ&W$öd6†FW'2„Æö6F–öâåF—FÆTçVÒÂgVÄçVÔöd6†FW'2’’“°Ð¢ÐÐ Ð¢òòvWBF÷FÂF–ÖRöbF—FÆPÐ¢EdEô„Õ4eõD”ÔT4ôDRF4GW#°Ð¢TÄôärVÄfÆw3°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWEF÷FÅF—FÆUF–ÖR‚gF4GW"ÂgVÄfÆw2’’’°Ð¢òò6Æ7VÆFRGW&F–öâ–â6V6öæG0Ð¢7G$GW"äf÷&ÖB„Â"VB"ÂF4GW"æ$†÷W'2¢c¢c²F4GW"æ$Ö–çWFW2¢c²F4GW"æ%6V6öæG2“°Ð¢ÐÐ Ð¢òò'V–ÆB7G&–æpÐ¢òòEdBÒ‡‡‡‡‡Æ7W'&VçGF—FÆWÆçVÖ&W&öf6†FW'7Æ7W'&VçF6†FW'ÇF—FÆVGW&F–öàÐ¢WF†÷"äf÷&ÖB„Â"VÇR"ÂÆö6F–öâåF—FÆTçVÒ“°Ð¢FW67&—F–öâäf÷&ÖB„Â"VÇR"ÂVÄçVÔöd6†FW'2“°Ð¢Æ&VÂäf÷&ÖB„Â"VÇR"ÂÆö6F–öâä6†FW$çVÒ“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢F—FÆRå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢WF†÷"å&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢FW67&—F–öâå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢Æ&VÂå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð Ð¢57G&–æur'Vfc°Ð¢'Vfbäf÷&ÖB„Â"W7ÂW7ÂW7ÂW7ÂW2"ÂF—FÆRävWE7G&–ær‚’ÂWF†÷"ävWE7G&–ær‚’ÂFW67&—F–öâävWE7G&–ær‚’ÂÆ&VÂävWE7G&–ær‚’Â7G$GW"ävWE7G&–ær‚’“°Ð Ð¢6VæD”6öÖÖæB„4ÔEôäõuÄ””ärÂÂ"W2"Â7FF–5ö67CÄÅ5u5E#â†'Vfb’“°Ð¢–b‡6VæGG&6¶–æfò’°Ð¢6VæE7V'F—FÆUG&6·5Fô’‚“°Ð¢6VæDVF–õG&6·5Fô’‚“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæE7V'F—FÆUG&6·5Fô’‚Ð§°Ð¢57G&–æur7G%7V'3°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢TÄôärVÅ7G&V×4f–Æ&ÆRÂVÄ7W'&VçE7G&VÓ°Ð¢$ôôÂ$—4F—6&ÆVC°Ð¢–b†Õ÷EdD’bb5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçE7V'–7GW&R‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒÂf$—4F—6&ÆVB’Ð¢bbVÅ7G&V×4f–Æ&ÆRâ’°Ð¢Ä4”BFVdÆæwVvS°Ð¢–çB•6VÆV7FVBÒÓ°Ð Ð¢EdEõ5T%”5EU$UôÄäuôU…BW‡C°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWDFVfVÇE7V'–7GW&TÆæwVvR‚dFVdÆæwVvRÂfW‡B’’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢f÷"…TÄôär’Ò²’ÂVÅ7G&V×4f–Æ&ÆS²’²²’°Ð¢Ä4”BÆæwVvS°Ð¢–b„d”ÄTB†Õ÷EdD’ÓävWE7V'–7GW&TÆæwVvR†’ÂdÆæwVvR’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†’ÓÒVÄ7W'&VçE7G&VÒ’°Ð¢•6VÆV7FVBÒ†–çB–“°Ð¢ÐÐ Ð¢57G&–ær7G#°Ð¢–b„ÆæwVvR’°Ð¢vWDÆö6ÆU7G&–ær„ÆæwVvRÂÄô4ÄUõ4TätÄäuTtRÂ7G"“°Ð¢ÒVÇ6R°Ð¢7G"äf÷&ÖB„”E5ôuõTä´äõtâÂ–çB†’²’“°Ð¢ÐÐ Ð¢EdEõ7V'–7GW&TGG&–'WFW2E#°Ð¢–b…5T44TTDTB†Õ÷EdD’ÓävWE7V'–7GW&TGG&–'WFW2†’ÂdE"’’’°Ð¢7v—F6‚„E"äÆæwVvTW‡FVç6–öâ’°Ð¢66REdEõ5ôU…Eôæ÷E7V6–f–VC Ð¢FVfVÇC Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåôæ÷&ÖÃ Ð¢7G"³ÒõB‚""“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåô&–s Ð¢7G"³ÒõB‚"„&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô6F–öåô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„6†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ôæ÷&ÖÃ Ð¢7G"³ÒõB‚"„42’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ô&–s Ð¢7G"³ÒõB‚"„42&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eô45ô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„426†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…Eôf÷&6VC Ð¢7G"³ÒõB‚"„f÷&6VB’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ôæ÷&ÖÃ Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ô&–s Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2Â&–r’"“°Ð¢'&V³°Ð¢66REdEõ5ôU…EôF—&V7F÷$6öÖÖVçG5ô6†–ÆG&Vã Ð¢7G"³ÒõB‚"„F—&V7F÷"6öÖÖVçG2Â6†–ÆG&Vâ’"“°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢–b‚7G%7V'2ä—4V×G’‚’’°Ð¢7G%7V'2äVæB„Â'Â"“°Ð¢ÐÐ¢7G"å&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢7G%7V'2äVæB‡7G"“°Ð¢ÐÐ¢–b„g„vWD6WGF–æw2‚’ædVæ&ÆU7V'F—FÆW2’°Ð¢7G%7V'2äVæDf÷&ÖB„Â'ÂVB"Â•6VÆV7FVB“°Ð¢ÒVÇ6R°Ð¢7G%7V'2äVæB„Â'ÂÓ"“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢–çB’ÒÂ•6VÆV7FVBÒÓ°Ð¢–b‡÷2’°Ð¢v†–ÆR‡÷2’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBç6÷W&6Tf–ÇFW"’°Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB‡54bÓä6÷VçB‚f57G&V×2’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢f÷"†–çB¢ÒÂ6çBÒ†–çB–57G&V×3²¢Â6çC²¢²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð¢t4„"¢7¤æÖRÒçVÆÇG#°Ð Ð¢–b„d”ÄTB‡54bÓä–æfò†¢ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’Ð¢ÇÂ7¤æÖR’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢57G&–æræÖR‡7¤æÖR“°Ð¢6õF6´ÖVÔg&VR‡7¤æÖR“°Ð Ð¢–b†Gtw&÷WÒ"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÐÐ¢bbGtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢•6VÆV7FVBÒ£°Ð¢ÐÐ Ð¢–b‚7G%7V'2ä—4V×G’‚’’°Ð¢7G%7V'2äVæB„Â'Â"“°Ð¢ÐÐ¢æÖRå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢7G%7V'2äVæB†æÖR“°Ð Ð¢’²³°Ð¢ÐÐ¢ÒVÇ6R°Ð¢46öÕG#Ä•7V%7G&VÓâ7V%7G&VÒÒ7V$–çWBç7V%7G&VÓ°Ð¢–b‚7V%7G&VÒ’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢•6VÆV7FVBÒ’²7V%7G&VÒÓävWE7G&VÒ‚“°Ð¢ÐÐ Ð¢f÷"†–çB¢ÒÂ6çBÒ7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“²¢Â6çC²¢²²’°Ð¢t4„"¢æÖRÒçVÆÇG#°Ð¢–b…5T44TTDTB‡7V%7G&VÒÓävWE7G&VÔ–æfò†¢ÂgæÖRÂçVÆÇG"’’’°Ð¢57G&–æræÖR‡æÖR“°Ð¢6õF6´ÖVÔg&VR‡æÖR“°Ð Ð¢–b‚7G%7V'2ä—4V×G’‚’’°Ð¢7G%7V'2äVæB„Â'Â"“°Ð¢ÐÐ¢æÖRå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢7G%7V'2äVæB†æÖR“°Ð¢ÐÐ¢’²³°Ð¢ÐÐ¢ÐÐ Ð¢ÐÐ¢–b„g„vWD6WGF–æw2‚’ædVæ&ÆU7V'F—FÆW2’°Ð¢7G%7V'2äVæDf÷&ÖB„Â'ÂVB"Â•6VÆV7FVB“°Ð¢ÒVÇ6R°Ð¢7G%7V'2äVæB„Â'ÂÓ"“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢7G%7V'2äVæB„Â"Ó"“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢7G%7V'2äVæB„Â"Ó""“°Ð¢ÐÐ¢6VæD”6öÖÖæB„4ÔEôÄ•5E5T%D•DÄUE$4µ2ÂÂ"W2"Â7FF–5ö67CÄÅ5u5E#â‡7G%7V'2’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæDVF–õG&6·5Fô’‚Ð§°Ð¢57G&–æur7G$VF–÷3°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢Etõ$B57G&V×2Ò°Ð¢–b†Õ÷VF–õ7v—F6†W%52bb5T44TTDTB†Õ÷VF–õ7v—F6†W%52Óä6÷VçB‚f57G&V×2’’’°Ð¢–çB7W'&VçE7G&VÒÒÓ°Ð¢f÷"†–çB’Ò²’Â†–çB–57G&V×3²’²²’°Ð¢ÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢Etõ$BGtfÆw2Ò°Ð¢Ä4”BÆ6–BÒ°Ð¢Etõ$BGtw&÷WÒ°Ð¢t4„"¢7¤æÖRÒçVÆÇG#°Ð¢–b„d”ÄTB†Õ÷VF–õ7v—F6†W%52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b†GtfÆw2ÓÒÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’°Ð¢7W'&VçE7G&VÒÒ“°Ð¢ÐÐ¢57G&–æræÖR‡7¤æÖR“°Ð¢–b‚7G$VF–÷2ä—4V×G’‚’’°Ð¢7G$VF–÷2äVæB„Â'Â"“°Ð¢ÐÐ¢æÖRå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢7G$VF–÷2äVæDf÷&ÖB„Â"W2"ÂæÖRävWE7G&–ær‚’“°Ð¢–b‡×B’°Ð¢FVÆWFTÖVF–G—R‡×B“°Ð¢ÐÐ¢–b‡7¤æÖR’°Ð¢6õF6´ÖVÔg&VR‡7¤æÖR“°Ð¢ÐÐ¢ÐÐ¢7G$VF–÷2äVæDf÷&ÖB„Â'ÂVB"Â7W'&VçE7G&VÒ“°Ð Ð¢ÒVÇ6R°Ð¢7G$VF–÷2äVæB„Â"Ó"“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢7G$VF–÷2äVæB„Â"Ó""“°Ð¢ÐÐ¢6VæD”6öÖÖæB„4ÔEôÄ•5DTD”õE$4µ2ÂÂ"W2"Â7FF–5ö67CÄÅ5u5E#â‡7G$VF–÷2’“°Ð Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæEÆ–Æ—7EFô’‚Ð§°Ð¢57G&–æur7G%Æ–Æ—7C°Ð¢õ4•D”ôâ÷2ÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWD†VE÷6—F–öâ‚’Â÷3#°Ð Ð¢v†–ÆR‡÷2’°Ð¢5Æ–Æ—7D—FVÒbÆ’ÒÕ÷væEÆ–Æ—7D&"æÕ÷ÂävWDæW‡B‡÷2“°Ð Ð¢–b‡Æ’æÕ÷G—RÓÒ5Æ–Æ—7D—FVÓ£¦f–ÆR’°Ð¢÷3"ÒÆ’æÕöfç2ävWD†VE÷6—F–öâ‚“°Ð¢v†–ÆR‡÷3"’°Ð¢57G&–ærfâÒÆ’æÕöfç2ävWDæW‡B‡÷3"“°Ð¢–b‚7G%Æ–Æ—7Bä—4V×G’‚’’°Ð¢7G%Æ–Æ—7BäVæB„Â'Â"“°Ð¢ÐÐ¢fâå&WÆ6R„Â'Â"ÂÂ%ÅÇÂ"“°Ð¢7G%Æ–Æ—7BäVæDf÷&ÖB„Â"W2"ÂfâävWE7G&–ær‚’“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b‡7G%Æ–Æ—7Bä—4V×G’‚’’°Ð¢7G%Æ–Æ—7BäVæB„Â"Ó"“°Ð¢ÒVÇ6R°Ð¢7G%Æ–Æ—7BäVæDf÷&ÖB„Â'ÂVB"ÂÕ÷væEÆ–Æ—7D&"ävWE6VÄ–G‚‚’“°Ð¢ÐÐ¢6VæD”6öÖÖæB„4ÔEõÄ”Ä•5BÂÂ"W2"Â7FF–5ö67CÄÅ5u5E#â‡7G%Æ–Æ—7B’“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæD7W'&VçE÷6—F–öåFô’†&ööÂdæ÷F–g•6VV²Ð§°Ð¢–b‚g„vWD6WGF–æw2‚’æ„Ö7FW%væB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢57G&–æur7G%÷3°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢$TdU$Tä4UõD”ÔR'D7W#°Ð¢Õ÷Õ2ÓävWD7W'&VçE÷6—F–öâ‚g'D7W"“°Ð¢7G%÷2äf÷&ÖB„Â"Rã6b"Â'D7W"òã“°Ð¢ÒVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdB’°Ð¢EdEõÄ”$4µôÄô4D”ôã"Æö6F–öã°Ð¢òòvWB7W'&VçBÆö6F–öâv†–ÆRÆ––ærF—62Âv–ÆÂ&WGW&âÂ–bBÖVçPÐ¢–b†Õ÷EdD’ÓävWD7W'&VçDÆö6F–öâ‚dÆö6F–öâ’ÓÒ5ôô²’°Ð¢7G%÷2äf÷&ÖB„Â"VB"ÂÆö6F–öâåF–ÖT6öFRæ$†÷W'2¢c¢c²Æö6F–öâåF–ÖT6öFRæ$Ö–çWFW2¢c²Æö6F–öâåF–ÖT6öFRæ%6V6öæG2“°Ð¢ÐÐ¢ÐÐ Ð¢6VæD”6öÖÖæB†dæ÷F–g•6VV²ò4ÔEôäõD”e•4TT²¢4ÔEô5U%$TåEõ4•D”ôâÂ7G%÷2“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæD7W'&VçEföÇVÖUFô’†&ööÂf÷&6RÐ§°Ð¢–b‚g„vWD6WGF–æw2‚’æ„Ö7FW%væB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢6öç7B–çBföÇVÖRÒvWEföÇVÖR‚“°Ð¢–b†f÷&6RÇÂföÇVÖRÒÕöÆ7D•föÇVÖR’°Ð¢–b†Õö†÷7D–çD•fW'6–öââ’°Ð¢òò†÷7B7V·2F†R–çFVvW"6†ææVÃ¢FVÆ—fW"æöâÖ&Æö6¶–ærÂæò'VffW"Fò¶VWÆ—fRàÐ¢÷7D”–çB„g„vWD6WGF–æw2‚’æ„Ö7FW%væBÂÕ4”åEô5U%$TåEdôÅTÔRÂföÇVÖR“°Ð¢ÕöÆ7D•föÇVÖRÒföÇVÖS°Ð¢ÒVÇ6R°Ð¢57G&–æur–ÆöC°Ð¢–ÆöBäf÷&ÖB„Â"VB"ÂföÇVÖR“°Ð¢òòöæÇ’ÆF6‚F†RfÇVRv†VâF†R†÷7B7GVÆÇ’&V6V—fVB—BÂ6ò6VæBF†@Ð¢òòF–ÖVB÷WBv–ç7B'W7’†÷7B—2&WG&–VBöâF†RæW‡B6†ævRàÐ¢–b…6VæD•7G&–æuFò„g„vWD6WGF–æw2‚’æ„Ö7FW%væBÂ4ÔEô5U%$TåEdôÅTÔRÂ–ÆöB’’°Ð¢ÕöÆ7D•föÇVÖRÒföÇVÖS°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæD7W'&VçD×WFUFô’†&ööÂf÷&6RÐ§°Ð¢–b‚g„vWD6WGF–æw2‚’æ„Ö7FW%væB’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢6öç7B–çB×WFRÒ—4×WFVB‚’ò¢°Ð¢–b†f÷&6RÇÂ×WFRÒÕöÆ7D”×WFR’°Ð¢–b†Õö†÷7D–çD•fW'6–öââ’°Ð¢÷7D”–çB„g„vWD6WGF–æw2‚’æ„Ö7FW%væBÂÕ4”åEô5U%$TåDÕUDRÂ×WFR“°Ð¢ÕöÆ7D”×WFRÒ×WFS°Ð¢ÒVÇ6R°Ð¢57G&–æur–ÆöC°Ð¢–ÆöBäf÷&ÖB„Â"VB"Â×WFR“°Ð¢–b…6VæD•7G&–æuFò„g„vWD6WGF–æw2‚’æ„Ö7FW%væBÂ4ÔEô5U%$TåDÕUDRÂ–ÆöB’’°Ð¢ÕöÆ7D”×WFRÒ×WFS°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥÷7D”–çB„…täB…F&vWBÂtõ$B6öÖÖæBÂ–çBfÇVRÐ§°Ð¢–b†…F&vWBbbtÕôÕ4•ô”åB’°Ð¢òòæöâÖ&Æö6¶–æs¢F†RfÇVRG&fVÇ2–ç6–FRF†RÖW76vRÂ6òF†W&R—2æò'VffW"FðÐ¢òò¶VWÆ—fRæBæòæVVBFòv—Bf÷"F†RF&vWBFò&ö6W72—B‡VæÆ–¶RtÕô4õ”DD’àÐ¢£¥÷7DÖW76vR†…F&vWBÂtÕôÕ4•ô”åBÂ&V–çFW'&WEö67CÅu$Óâ„vWE6fT‡væB‚’’ÀÐ¢Õ4•ô”åEôÔ´TÅ$Ò‡fÇVRÂ6öÖÖæB’“°Ð¢ÐÐ§ÐÐ Ð¢òòÖ†÷7BÓäÕ2–çFVvW"6öÖÖæBFò—G2tÕô4õ”DDWV—fÆVçBƒ–bæ÷B”åBÖ&ÆR’àÐ§7FF–2Õ4•ô4ôÔÔäB–çD6öÖÖæEFô’…tõ$B–çD6ÖBÐ§°Ð¢7v—F6‚†–çD6ÖB’°Ð¢66RÕ4”åEõ4UEdôÅTÔS¢&WGW&â4ÔEõ4UEdôÅTÔS°Ð¢66RÕ4”åEõ4UDÕUDS¢&WGW&â4ÔEõ4UDÕUDS°Ð¢66RÕ4”åEôtUEdôÅTÔS¢&WGW&â4ÔEôtUEdôÅTÔS°Ð¢66RÕ4”åEôtUDÕUDS¢&WGW&â4ÔEôtUDÕUDS°Ð¢66RÕ4”åEõ5Dõ¢&WGW&â4ÔEõ5Dõ°Ð¢66RÕ4”åEô4Äõ4Td”ÄS¢&WGW&â4ÔEô4Äõ4Td”ÄS°Ð¢66RÕ4”åEõÄ•U4S¢&WGW&â4ÔEõÄ•U4S°Ð¢66RÕ4”åEõÄ“¢&WGW&â4ÔEõÄ“°Ð¢66RÕ4”åEõU4S¢&WGW&â4ÔEõU4S°Ð¢66RÕ4”åEô4ÄT%Ä”Ä•5C¢&WGW&â4ÔEô4ÄT%Ä”Ä•5C°Ð¢66RÕ4”åEõ5D%EÄ”Ä•5C¢&WGW&â4ÔEõ5D%EÄ”Ä•5C°Ð¢66RÕ4”åEõDôttÄTeTÄÅ45$TTã¢&WGW&â4ÔEõDôttÄTeTÄÅ45$TTã°Ð¢66RÕ4”åEô¥TÕdõ%t$DÔTC¢&WGW&â4ÔEô¥TÕdõ%t$DÔTC°Ð¢66RÕ4”åEô¥TÕ$4µt$DÔTC¢&WGW&â4ÔEô¥TÕ$4µt$DÔTC°Ð¢66RÕ4”åEô”ä5$T4UdôÅTÔS¢&WGW&â4ÔEô”ä5$T4UdôÅTÔS°Ð¢66RÕ4”åEôDT5$T4UdôÅTÔS¢&WGW&â4ÔEôDT5$T4UdôÅTÔS°Ð¢66RÕ4”åEõ4„DU%õDôttÄS¢&WGW&â4ÔEõ4„DU%õDôttÄS°Ð¢66RÕ4”åEô4Äõ4T¢&WGW&â4ÔEô4Äõ4T°Ð¢66RÕ4”åEõ4UDTD”õE$4³¢&WGW&â4ÔEõ4UDTD”õE$4³°Ð¢66RÕ4”åEõ4UE5T%D•DÄUE$4³¢&WGW&â4ÔEõ4UE5T%D•DÄUE$4³°Ð¢66RÕ4”åEô¥TÕôdå4T4ôäE3¢&WGW&â4ÔEô¥TÕôdå4T4ôäE3°Ð¢66RÕ4”åEõ4UDTD”ôDTÄ“¢&WGW&â4ÔEõ4UDTD”ôDTÄ“°Ð¢66RÕ4”åEõ4UE5T%D•DÄTDTÄ“¢&WGW&â4ÔEõ4UE5T%D•DÄTDTÄ“°Ð¢66RÕ4”åEôtUD5U%$TåDTD”õE$4³¢&WGW&â4ÔEôtUD5U%$TåDTD”õE$4³°Ð¢66RÕ4”åEôtUD5U%$TåE5T%D•DÄUE$4³§&WGW&â4ÔEôtUD5U%$TåE5T%D•DÄUE$4³°Ð¢FVfVÇC¢&WGW&â7FF–5ö67CÄÕ4•ô4ôÔÔäCâƒ“°Ð¢ÐÐ§ÐÐ Ð¢òòÖÕ2Óæ†÷7Bæ÷F–f–6F–öâFò—G2–çFVvW"Ö6†ææVÂ6öÖÖæBƒ–bæ÷B”åBÖ&ÆR’àÐ§7FF–2tõ$B”6öÖÖæEFô–çB„Õ4•ô4ôÔÔäB6ÖBÐ§°Ð¢7v—F6‚†6ÖB’°Ð¢66R4ÔEô5U%$TåEdôÅTÔS¢&WGW&âÕ4”åEô5U%$TåEdôÅTÔS°Ð¢66R4ÔEô5U%$TåDÕUDS¢&WGW&âÕ4”åEô5U%$TåDÕUDS°Ð¢66R4ÔEõ5DDS¢&WGW&âÕ4”åEõ5DDS°Ð¢66R4ÔEõÄ”ÔôDS¢&WGW&âÕ4”åEõÄ”ÔôDS°Ð¢66R4ÔEô5U%$TåDTD”õE$4³¢&WGW&âÕ4”åEô5U%$TåDTD”õE$4³°Ð¢66R4ÔEô5U%$TåE5T%D•DÄUE$4³¢&WGW&âÕ4”åEô5U%$TåE5T%D•DÄUE$4³°Ð¢FVfVÇC¢&WGW&â°Ð¢ÐÐ§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öä”–çDÖW76vR…u$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢6öç7B…täB…6VæFW"Ò&V–çFW'&WEö67CÄ…täCâ‡u&Ò“°Ð¢6öç7Btõ$B6öÖÖæBÒÕ4•ô”åEô4ôÔÔäEôôb†Å&Ò“°Ð¢6öç7B–çBfÇVRÒÕ4•ô”åEõdÅTUôôb†Å&Ò“°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢òòWfW'’–çFVvW"6öÖÖæB—2†öæ÷&VBöæÇ’g&öÒF†R6öææV7FVB†÷7B‡6ÖRvFR2F†PÐ¢òòtÕô4õ”DD6WGFW'2’â„TÄÄòW7F&Æ—6†W2F†BF†R†÷7B7V·2F†—26†ææVÂàÐ¢–b†…6VæFW"Ò2æ„Ö7FW%væB’°Ð¢&WGW&â°Ð¢ÐÐ Ð¢–b†6öÖÖæBÓÒÕ4”åEô„TÄÄò’°Ð¢Õö†÷7D–çD•fW'6–öâÒfÇVS°Ð¢÷7D”–çB†…6VæFW"ÂÕ4”åEô„TÄÄòÂÕ4•ô”åEõdU%4”ôâ“°Ð¢&WGW&â°Ð¢ÐÐ Ð¢òò&WW6R&ö6W74”6öÖÖæB6òâ–çFVvW"6öÖÖæB6†&W2W†7FÇ’F†R6ÖR†æFÆ–æræ@Ð¢òò6VæFW"vF–ær2—G2tÕô4õ”DDf÷&Ó²F†RfÇVR—276VB2F†R7G&–ær&ÖWFW"àÐ¢6öç7BÕ4•ô4ôÔÔäB6ÖBÒ–çD6öÖÖæEFô’†6öÖÖæB“°Ð¢–b†6ÖB’°Ð¢57G&–æur–ÆöC°Ð¢–ÆöBäf÷&ÖB„Â"VB"ÂfÇVR“²òò–væ÷&VB'’&ÖWFW&ÆW726öÖÖæG0Ð¢4õ”DD5E%T5B6G2Ò·Ó°Ð¢6G2æGtFFÒ6ÖC°Ð¢6G2æ6$FFÒ7FF–5ö67CÄEtõ$Câ‚‡–ÆöBävWDÆVæwF‚‚’²’¢6—¦Vöb‡v6†%÷B’“°Ð¢6G2æÇFFÒ6öç7Eö67CÇv6†%÷B£â‡–ÆöBävWE7G&–ær‚’“°Ð¢&ö6W74”6öÖÖæB†…6VæFW"Âf6G2“°Ð¢ÐÐ¢&WGW&â°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6VæD”æ÷F–g’„Õ4•ô4ôÔÔäB6ÖBÂ–çBfÇVRÐ§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢–b‚2æ„Ö7FW%væB’°Ð¢&WGW&ã°Ð¢ÐÐ¢6öç7Btõ$B–çD6ÖBÒ”6öÖÖæEFô–çB†6ÖB“°Ð¢–b†Õö†÷7D–çD•fW'6–öââbb–çD6ÖB’°Ð¢÷7D”–çB‡2æ„Ö7FW%væBÂ–çD6ÖBÂfÇVR“°Ð¢ÒVÇ6R°Ð¢6VæD”6öÖÖæB†6ÖBÂÂ"VB"ÂfÇVR“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥6†÷tõ4D7W7FöÔÖW76vT’†6öç7BÕ5ôõ4DDD¢÷6DFFÐ§°Ð¢òò7G$×6r—2f—†VB×6—¦Rf–VÆB–â†÷7B×7WÆ–VB'VffW#²&÷VæBF†R&VB6òÐ¢òòæöâ×FW&Ö–æFVBf–VÆB6ææ÷B÷fW"×&VB7BF†R7G'V7BàÐ¢6öç7B57G&–æur×6r†÷6DFFÓç7G$×6rÂ7FF–5ö67CÆ–çCâ‡v76æÆVâ†÷6DFFÓç7G$×6rÂö6÷VçFöb†÷6DFFÓç7G$×6r’’’“°Ð¢Õôõ4BäF—7Æ”ÖW76vR‚„õ4EôÔU54tUõ2–÷6DFFÓæä×6u÷2Â×6rÂ÷6DFFÓæäGW&F–öäÕ2“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤§V×ödå6V6öæG2†–çBå6V6öæG2Ð§°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢$TdU$Tä4UõD”ÔR'D7W#°Ð Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄR’°Ð¢Õ÷Õ2ÓävWD7W'&VçE÷6—F–öâ‚g'D7W"“°Ð¢EdEô„Õ4eõD”ÔT4ôDRF47W"Ò%C$„Õ4b‡'D7W"“°Ð¢ÆöærÅ÷6—F–öâÒF47W"æ$†÷W'2¢c¢c²F47W"æ$Ö–çWFW2¢c²F47W"æ%6V6öæG2²å6V6öæG3°Ð Ð¢òò&WfW'BF†RWFFR÷6—F–öâFò$TdU$Tä4UõD”ÔRf÷&Ö@Ð¢F47W"æ$†÷W'2Ò„%•DR’†Å÷6—F–öâò3c“°Ð¢F47W"æ$Ö–çWFW2Ò†Å÷6—F–öâòc’Rc°Ð¢F47W"æ%6V6öæG2ÒÅ÷6—F–öâRc°Ð¢'D7W"Ò„Õ4c%%B‡F47W"“°Ð Ð¢òòV–6²æBF—'G’G&–6³ Ð¢òòW6RÓç6VV·FòÓçÆ’6VV×2Fò&WfVçG26öÖR7G&ævPÐ¢òòf–FVòVffV7B†W‚âÆö6·2f÷"v†–ÆRæBF†â'Vææ–ærf7BÐ¢–b‚ÕödVF–ôöæÇ’’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢ÐÐ¢6VVµFò‡'D7W"“°Ð¢–b‚ÕödVF–ôöæÇ’’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ’“°Ð¢òò6†÷r7W'&VçB÷6—F–öâ÷fW'&–FFVâ'’Æ’6öÖÖæ@Ð¢Õôõ4BäF—7Æ”ÖW76vR„õ4EõDõÄTeBÂÕ÷væE7FGW4&"ävWE7FGW5F–ÖW"‚’Â#“°Ð¢ÐÐ¢ÐÐ¢ÐÐ§ÐÐ Ð¢òòDôDò¢Fò&Rf–æ—6†VBÐ¢ò÷fö–B4Ö–äg&ÖS£¤WFõ6VÆV7EG&6·2‚Ð¢ò÷°Ð¢òòÄ4”BFVdVF–ôÆæwVvTÆ6–B³%ÒÒ´Ô´TÄ4”B‚Ô´TÄät”B„Ääuôe$Tä4‚Â5T$ÄäuôDTdTÅB’Â4õ%EôDTdTÅB’ÂÔ´TÄ4”B‚Ô´TÄät”B„ÄäuôTätÄ•4‚Â5T$ÄäuôDTdTÅB’Â4õ%EôDTdTÅB—Ó°Ð¢òò–çBFVdVF–ôÆæwVvT–æFW‚³%ÒÒ²ÓÂÓÓ°Ð¢òòÄ4”BFVe7V'F—FÆTÆæwVvTÆ6–B³%ÒÒ³ÂÔ´TÄ4”B‚Ô´TÄät”B„Ääuôe$Tä4‚Â5T$ÄäuôDTdTÅB’Â4õ%EôDTdTÅB—Ó°Ð¢òò–çBFVe7V'F—FÆTÆæwVvT–æFW…³%ÒÒ²ÓÂÓÓ°Ð¢òòÄ4”BÆæwVvRÒÔ´TÄ4”B„Ô´TÄät”B„Ääuôe$Tä4‚Â5T$ÄäuôDTdTÅB’Â4õ%EôDTdTÅB“°Ð¢òðÐ¢òò–b‚†Õö”ÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôD”är’ÇÂ†Õö”ÖVF–ÆöE7FFRÓÒÔÅ3£¤ÄôDTB’Ð¢òò°Ð¢òò–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôd”ÄRÐ¢òò°Ð¢òò46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ52Òf–æDf–ÇFW"…õ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’ÂÕ÷t"“°Ð¢òðÐ¢òòEtõ$B57G&V×2Ò°Ð¢òò–b‡52bb5T44TTDTB‡52Óä6÷VçB‚f57G&V×2’’Ð¢òò°Ð¢òòf÷"†–çB’Ò²’Â†–çB–57G&V×3²’²²Ð¢òò°Ð¢òòÕôÔTD”õE•R¢×BÒçVÆÇG#°Ð¢òòEtõ$BGtfÆw2Ò°Ð¢òòÄ4”BÆ6–BÒ°Ð¢òòEtõ$BGtw&÷WÒ°Ð¢òòt4„"¢7¤æÖRÒçVÆÇG#°Ð¢òò–b„d”ÄTB‡52Óä–æfò†’Âg×BÂfGtfÆw2ÂfÆ6–BÂfGtw&÷WÂg7¤æÖRÂçVÆÇG"ÂçVÆÇG"’’Ð¢òò&WGW&ã°Ð¢òòÐÐ¢òòÐÐ¢òðÐ¢òòõ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢òòv†–ÆR‡÷2Ð¢òò°Ð¢òò46öÕG#Ä•7V%7G&VÓâ7V%7G&VÒÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2’ç7V%7G&VÓ°Ð¢òò–b‚7V%7G&VÒ’6öçF–çVS°Ð¢òðÐ¢òòf÷"†–çB’ÒÂ¢Ò7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“²’Â£²’²²Ð¢òò°Ð¢òòt4„"¢æÖRÒçVÆÇG#°Ð¢òò–b…5T44TTDTB‡7V%7G&VÒÓävWE7G&VÔ–æfò†’ÂgæÖRÂdÆæwVvR’’Ð¢òò°Ð¢òò–b„FVdVF–ôÆæwVvTÆ6–E³ÒÓÒÆæwVvR’FVe7V'F—FÆTÆæwVvT–æFW…³ÒÒ“°Ð¢òò–b„FVe7V'F—FÆTÆæwVvTÆ6–E³ÒÓÒÆæwVvR’FVe7V'F—FÆTÆæwVvT–æFW…³ÒÒ“°Ð¢òò6õF6´ÖVÔg&VR‡æÖR“°Ð¢òòÐÐ¢òòÐÐ¢òòÐÐ¢òòÐÐ¢òòVÇ6R–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBÐ¢òò°Ð¢òòTÄôärVÅ7G&V×4f–Æ&ÆRÂVÄ7W'&VçE7G&VÓ°Ð¢òò$ôôÂ$—4F—6&ÆVC°Ð¢òðÐ¢òò–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçE7V'–7GW&R‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒÂf$—4F—6&ÆVB’’Ð¢òò°Ð¢òòf÷"…TÄôär’Ò²’ÂVÅ7G&V×4f–Æ&ÆS²’²²Ð¢òò°Ð¢òòEdEõ7V'–7GW&TGG&–'WFW2E#°Ð¢òò–b…5T44TTDTB†Õ÷EdD’ÓävWE7V'–7GW&TÆæwVvR†’ÂdÆæwVvR’’Ð¢òò°Ð¢òòòòWFò6VÆV7Bf÷&6VB7V'F—FÆPÐ¢òò–b‚„FVdVF–ôÆæwVvTÆ6–E³ÒÓÒÆæwVvR’bb„E"äÆæwVvTW‡FVç6–öâÓÒEdEõ5ôU…Eôf÷&6VB’Ð¢òòFVe7V'F—FÆTÆæwVvT–æFW…³ÒÒ“°Ð¢òðÐ¢òò–b„FVe7V'F—FÆTÆæwVvTÆ6–E³ÒÓÒÆæwVvR’FVe7V'F—FÆTÆæwVvT–æFW…³ÒÒ“°Ð¢òòÐÐ¢òòÐÐ¢òòÐÐ¢òðÐ¢òò–b…5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçDVF–ò‚gVÅ7G&V×4f–Æ&ÆRÂgVÄ7W'&VçE7G&VÒ’’Ð¢òò°Ð¢òòf÷"…TÄôär’Ò²’ÂVÅ7G&V×4f–Æ&ÆS²’²²Ð¢òò°Ð¢òò–b…5T44TTDTB†Õ÷EdD’ÓävWDVF–ôÆæwVvR†’ÂdÆæwVvR’’Ð¢òò°Ð¢òò–b„FVdVF–ôÆæwVvTÆ6–E³ÒÓÒÆæwVvR’FVdVF–ôÆæwVvT–æFW…³ÒÒ“°Ð¢òò–b„FVdVF–ôÆæwVvTÆ6–E³ÒÓÒÆæwVvR’FVdVF–ôÆæwVvT–æFW…³ÒÒ“°Ð¢òòÐÐ¢òòÐÐ¢òòÐÐ¢òðÐ¢òòòò6VÆV7B&W7BVF–ò÷7V'F—FÆW2G&6·0Ð¢òò–b„FVdVF–ôÆæwVvTÆ6–E³ÒÒÓÐ¢òò°Ð¢òòÕ÷EdD2Óå6VÆV7DVF–õ7G&VÒ„FVdVF–ôÆæwVvT–æFW…³ÒÂEdEô4ÔEôdÄuô&Æö6²ÂçVÆÇG"“°Ð¢òò–b„FVe7V'F—FÆTÆæwVvT–æFW…³ÒÒÓÐ¢òòÕ÷EdD2Óå6VÆV7E7V'–7GW&U7G&VÒ„FVe7V'F—FÆTÆæwVvT–æFW…³ÒÂEdEô4ÔEôdÄuô&Æö6²ÂçVÆÇG"“°Ð¢òòÐÐ¢òòVÇ6R–b‚„FVdVF–ôÆæwVvTÆ6–E³ÒÒÓ’bb„FVe7V'F—FÆTÆæwVvTÆ6–E³ÒÒÓ’Ð¢òò°Ð¢òòÕ÷EdD2Óå6VÆV7DVF–õ7G&VÒ„FVdVF–ôÆæwVvT–æFW…³ÒÂEdEô4ÔEôdÄuô&Æö6²ÂçVÆÇG"“°Ð¢òòÕ÷EdD2Óå6VÆV7E7V'–7GW&U7G&VÒ„FVe7V'F—FÆTÆæwVvT–æFW…³ÒÂEdEô4ÔEôdÄuô&Æö6²ÂçVÆÇG"“°Ð¢òòÐÐ¢òòÐÐ¢òðÐ¢òðÐ¢òòÐÐ¢ò÷ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öäf–ÆT÷VæF—&V7F÷'’‚Ð§°Ð¢–b‚—57FFT6Æ÷6VD÷$ÆöFVB‚’ÇÂ—5v–æF÷r†Õ÷væEÆ–Æ—7D&"’’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð¢57G&–ær7G%F—FÆR…7G%&W2„”E5ôÔ”äe$ÕôD•%õD•DÄR’“°Ð¢57G&–ærFƒ°Ð Ð¢Õ4föÆFW%–6¶W$F–ÆörfB„f÷&6UG&–Æ–æu6Æ6‚‡2æÆ7Df–ÆT÷VäF—%F‚’Âdõ5õD„ÕU5DU„•5BÂvWDÖöFÅ&VçB‚’Â”E5ôÔ”äe$ÕôD•%ô4„T4²“°Ð¢fBæÕööfâæÇ7G%F—FÆRÒ7G%F—FÆS°Ð Ð¢–b†fBäFôÖöFÂ‚’ÓÒ”Dô²’°Ð¢F‚ÒfBävWEF„æÖR‚“²òövWFföÆFW'F‚‚’FöW2æ÷Bv÷&²6÷'&V7FÇ’f÷"4föÆFW%–6¶W$F–ÆöpÐ¢ÒVÇ6R°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢$ôôÂ&V7W"ÒE%TS°Ð¢fBävWD6†V6´'WGFöå7FFR„”E5ôÔ”äe$ÕôD•%ô4„T4²Â&V7W"“°Ð¢4÷VäF—$†VÇW#£¦Õö–æ6Å÷7V&F—"Ò&V7W#°Ð Ð¢òò–bvRv÷BÆ–æ²f–ÆRF†Bö–çG2FòF—&V7F÷'’ÂföÆÆ÷rF†RÆ–æ°Ð¢–b…F…WF–Ç3£¤—4Æ–æ´f–ÆR‡F‚’’°Ð¢57G&–ær&W6öÇfVEF‚ÒF…WF–Ç3£¥&W6öÇfTÆ–æ´f–ÆR‡F‚“°Ð¢–b…F…WF–Ç3£¤—4F—"‡&W6öÇfVEF‚’’°Ð¢F‚Ò&W6öÇfVEFƒ°Ð¢ÐÐ¢ÐÐ Ð¢F‚Òf÷&6UG&–Æ–æu6Æ6‚‡F‚“°Ð¢2æÆ7Df–ÆT÷VäF—%F‚ÒFƒ°Ð Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð¢6ÂäFEF–Â‡F‚“°Ð¢–b„4÷VäF—$†VÇW#£¦Õö–æ6Å÷7V&F—"’°Ð¢F…WF–Ç3£¥&V7W'6TFDF—"‡F‚Â6Â“°Ð¢ÐÐ Ð¢Õ÷væEÆ–Æ—7D&"ä÷Vâ‡6ÂÂG'VR“°Ð¢÷Vä7W%Æ–Æ—7D—FVÒ‚“°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¤7&VFUF‡VÖ&æ–ÅFööÆ&"‚Ð§°Ð¢–b‚F†—2ÇÂg„vWD6WGF–æw2‚’æ%W6TVæ†æ6VEF6´&"’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢–b‚Õ÷F6¶&$Æ—7B’°Ð¢–b…5T44TTDTB†Õ÷F6¶&$Æ—7Bä6ô7&VFT–ç7Fæ6R„4Å4”EõF6¶&$Æ—7BÂçVÆÇG"Â4Å45E…ô”å$ô5õ4U%dU"’’’°Ð¢–b„d”ÄTB†Õ÷F6¶&$Æ—7BÓä‡$–æ—B‚’’’°Ð¢Õ÷F6¶&$Æ—7Bå&VÆV6R‚“°Ð¢g„vWD6WGF–æw2‚’æ%W6TVæ†æ6VEF6´&"ÒfÇ6S°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢–b†Õ÷F6¶&$Æ—7B’°Ð¢&ööÂ%%DÄÆ–÷WBÒfÇ6S²òò77VÖRÆVgB×Fò×&–v‡BÆ–÷WB'’FVfVÇ@Ð¢òòG'’FòÆö6FRF†Rv–æF÷rW6VBFòF—7Æ’F†RF6²& Ð¢–b„5væB¢F6´&%væBÒf–æEv–æF÷r…õB‚%F6´Æ—7EF‡VÖ&æ–ÅvæB"’ÂçVÆÇG"’’°Ð¢%%DÄÆ–÷WBÒ‡F6´&%væBÓävWDW…7G–ÆR‚’bu5ôU…ôÄ”õUE%DÂ“°Ð¢ÐÐ Ð¢4Õ5æt–ÖvR–ÖvS°Ð¢–b‚–ÖvRäÆöB„”Deõt”ãuõDôôÄ$"’’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢56—¦R6—¦RÒ–ÖvRävWE6—¦R‚“°Ð Ð¢–b†%%DÄÆ–÷WB’²òòvRFöâwBvçBF†R'WGFöç2Fò&RÖ—'&÷&VB6òvR&RÖÖ—'&÷"F†VÐÐ¢òò7&VFRÖVÖ÷'’D72f÷"F†R6÷W&6RæBFW7F–æF–öâ&—FÖ0Ð¢4D26÷W&6TD2ÂFW7DD3°Ð¢6÷W&6TD2ä7&VFT6ö×F–&ÆTD2†çVÆÇG"“°Ð¢FW7DD2ä7&VFT6ö×F–&ÆTD2†çVÆÇG"“°Ð¢òò7vF†R6÷W&6R&—FÖv—F‚âV×G’öæPÐ¢4&—FÖ6÷W&6T–Ös°Ð¢6÷W&6T–ÖräGF6‚†–ÖvRäFWF6‚‚’“°Ð¢òò7&VFRFV×÷&'’D0Ð¢46Æ–VçDD26Æ–VçDD2†çVÆÇG"“°Ð¢òò7&VFRF†RFW7F–æF–öâ&—FÖ Ð¢–ÖvRä7&VFT6ö×F–&ÆT&—FÖ‚f6Æ–VçDD2Â6—¦Ræ7‚Â6—¦Ræ7’“°Ð¢òò6VÆV7BF†R&—FÖ2–çFòF†RD70Ð¢„tD”ô$¢öÆE6÷W&6TD4ö&¢Ò6÷W&6TD2å6VÆV7Dö&¦V7B‡6÷W&6T–Ör“°Ð¢„tD”ô$¢öÆDFW7DD4ö&¢ÒFW7DD2å6VÆV7Dö&¦V7B†–ÖvR“°Ð¢òò7GVÆÇ’fÆ—F†R&—FÖ Ð¢FW7DD2å7G&WF6„&ÇBƒÂÂ6—¦Ræ7‚Â6—¦Ræ7’ÀÐ¢g6÷W&6TD2Â6—¦Ræ7‚ÂÂ×6—¦Ræ7‚Â6—¦Ræ7’ÀÐ¢5$44õ’“°Ð¢òò&W6VÆV7BF†RöÆBö&¦V7G2&6²–çFòF†V—"D70Ð¢6÷W&6TD2å6VÆV7Dö&¦V7B†öÆE6÷W&6TD4ö&¢“°Ð¢FW7DD2å6VÆV7Dö&¦V7B†öÆDFW7DD4ö&¢“°Ð Ð¢6÷W&6TD2äFVÆWFTD2‚“°Ð¢FW7DD2äFVÆWFTD2‚“°Ð¢ÐÐ Ð¢4–ÖvTÆ—7B–ÖvTÆ—7C°Ð¢–ÖvTÆ—7Bä7&VFR‡6—¦Ræ7’Â6—¦Ræ7’Â”Ä5ô4ôÄõ#3"Â6—¦Ræ7‚ò6—¦Ræ7’Â“°Ð¢–ÖvTÆ—7BäFB‚f–ÖvRÂçVÆÇG"“°Ð Ð¢–b…5T44TTDTB†Õ÷F6¶&$Æ—7BÓåF‡VÖ$&%6WD–ÖvTÆ—7B†Õö…væBÂ–ÖvTÆ—7BävWE6fT†æFÆR‚’’’’°Ð¢D…TÔ$%UEDôâ'WGFöç5³UÒÒ·Ó°Ð Ð¢f÷"‡6—¦U÷B’Ò²’Âö6÷VçFöb†'WGFöç2“²’²²’°Ð¢'WGFöç5¶•ÒæGtÖ6²ÒD„%ô$•DÔÂD„%õDôôÅD•ÂD„%ôdÄu3°Ð¢'WGFöç5¶•ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢'WGFöç5¶•Òæ”&—FÖÒ²òòv–ÆÂ&R6WBÆFW Ð¢ÐÐ Ð¢òò$Ud”õU0Ð¢'WGFöç5³Òæ”–BÒ”ED%ô%UEDôã3°Ð¢òò5Dõ Ð¢'WGFöç5³Òæ”–BÒ”ED%ô%UEDôã°Ð¢òòÄ’õU4PÐ¢'WGFöç5³%Òæ”–BÒ”ED%ô%UEDôã#°Ð¢òòäU…@Ð¢'WGFöç5³5Òæ”–BÒ”ED%ô%UEDôãC°Ð¢òòeTÄÅ45$TTàÐ¢'WGFöç5³EÒæ”–BÒ”ED%ô%UEDôãS°Ð Ð¢–b†%%DÄÆ–÷WB’²òòvRFöâwBvçBF†R'WGFöç2Fò&RÖ—'&÷&VB6òvR&RÖÖ—'&÷"F†VÐÐ¢7FC£§&WfW'6R†'WGFöç2Â'WGFöç2²ö6÷VçFöb†'WGFöç2’“°Ð¢ÐÐ Ð¢–b…5T44TTDTB†Õ÷F6¶&$Æ—7BÓåF‡VÖ$&$FD'WGFöç2†Õö…væBÂö6÷VçFöb†'WGFöç2’Â'WGFöç2’’’°Ð¢&WGW&âWFFUF‡VÖ&$'WGFöâ‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&âUôd”Ã°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥WFFUF‡VÖ&$'WGFöâ‚Ð§°Ð¢Õ5õÄ•5DDR7FFRÒ5õ5Dõ°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢7v—F6‚„vWDÖVF–7FFR‚’’°Ð¢66R7FFUõ'Vææ–æs Ð¢7FFRÒ5õÄ“°Ð¢'&V³°Ð¢66R7FFUõW6VC Ð¢7FFRÒ5õU4S°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢&WGW&âWFFUF‡VÖ&$'WGFöâ‡7FFR“°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥WFFUF‡VÖ&$'WGFöâ„Õ5õÄ•5DDR•Æ•7FFRÐ§°Ð¢–b‚Õ÷F6¶&$Æ—7B’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢D…TÔ$%UEDôâ'WGFöç5³UÒÒ·Ó°Ð Ð¢f÷"‡6—¦U÷B’Ò²’Âö6÷VçFöb†'WGFöç2“²’²²’°Ð¢'WGFöç5¶•ÒæGtÖ6²ÒD„%ô$•DÔÂD„%õDôôÅD•ÂD„%ôdÄu3°Ð¢ÐÐ Ð¢'WGFöç5³Òæ”–BÒ”ED%ô%UEDôã3°Ð¢'WGFöç5³Òæ”–BÒ”ED%ô%UEDôã°Ð¢'WGFöç5³%Òæ”–BÒ”ED%ô%UEDôã#°Ð¢'WGFöç5³5Òæ”–BÒ”ED%ô%UEDôãC°Ð¢'WGFöç5³EÒæ”–BÒ”ED%ô%UEDôãS°Ð Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢–b‚2æ%W6TVæ†æ6VEF6´&"’°Ð¢Õ÷F6¶&$Æ—7BÓå6WD÷fW&Æ”–6öâ†Õö…væBÂçVÆÇG"ÂÂ""“°Ð¢Õ÷F6¶&$Æ—7BÓå6WE&öw&W757FFR†Õö…væBÂD%eôäõ$ôu$U52“°Ð Ð¢f÷"‡6—¦U÷B’Ò²’Âö6÷VçFöb†'WGFöç2“²’²²’°Ð¢'WGFöç5¶•ÒæGtfÆw2ÒD„$eô„”DDTã°Ð¢ÐÐ¢ÒVÇ6R°Ð¢'WGFöç5³Òæ”&—FÖÒ°Ð¢7G&–æt66„6÷’†'WGFöç5³Òç7¥F—Âö6÷VçFöb†'WGFöç5³Òç7¥F—’Â&W57G"„”E5ôuõ$Ud”õU2’“°Ð Ð¢'WGFöç5³Òæ”&—FÖÒ°Ð¢7G&–æt66„6÷’†'WGFöç5³Òç7¥F—Âö6÷VçFöb†'WGFöç5³Òç7¥F—’Â&W57G"„”E5ôuõ5Dõ’“°Ð Ð¢'WGFöç5³%Òæ”&—FÖÒ3°Ð¢7G&–æt66„6÷’†'WGFöç5³%Òç7¥F—Âö6÷VçFöb†'WGFöç5³%Òç7¥F—’Â&W57G"„”E5ôuõÄ•U4R’“°Ð Ð¢'WGFöç5³5Òæ”&—FÖÒC°Ð¢7G&–æt66„6÷’†'WGFöç5³5Òç7¥F—Âö6÷VçFöb†'WGFöç5³5Òç7¥F—’Â&W57G"„”E5ôuôäU…B’“°Ð Ð¢'WGFöç5³EÒæ”&—FÖÒS°Ð¢7G&–æt66„6÷’†'WGFöç5³EÒç7¥F—Âö6÷VçFöb†'WGFöç5³EÒç7¥F—’Â&W57G"„”E5ôuôeTÄÅ45$TTâ’“°Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢„”4ôâ„–6öâÒçVÆÇG#°Ð Ð¢'WGFöç5³ÒæGtfÆw2Ò‚2æeW6U6V&6„–äföÆFW"bbÕ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’ÃÒbb†Õ÷4"bbÕ÷4"Óä6†vWD6÷VçB‚’ÃÒ’’òD„$eôD•4$ÄTB¢D„$eôTä$ÄTC°Ð¢'WGFöç5³5ÒæGtfÆw2Ò‚2æeW6U6V&6„–äföÆFW"bbÕ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’ÃÒbb†Õ÷4"bbÕ÷4"Óä6†vWD6÷VçB‚’ÃÒ’’òD„$eôD•4$ÄTB¢D„$eôTä$ÄTC°Ð¢'WGFöç5³EÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð Ð¢–b†•Æ•7FFRÓÒ5õÄ’’°Ð¢'WGFöç5³ÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð¢'WGFöç5³%ÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð¢'WGFöç5³%Òæ”&—FÖÒ#°Ð Ð¢„–6öâÒ„„”4ôâ”ÆöD–ÖvR„g„vWD–ç7Fæ6T†æFÆR‚’ÂÔ´T”åE$U4õU$4R„”E%õD%õÄ’’Â”ÔtUô”4ôâÂÂÂÅ%ôDTdTÅE4•¤R“°Ð¢Õ÷F6¶&$Æ—7BÓå6WE&öw&W757FFR†Õö…væBÂÕ÷væE6VV´&"ä†4GW&F–öâ‚’òD%eôäõ$ÔÂ¢D%eôäõ$ôu$U52“°Ð¢ÒVÇ6R–b†•Æ•7FFRÓÒ5õ5Dõ’°Ð¢'WGFöç5³ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢'WGFöç5³%ÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð¢'WGFöç5³%Òæ”&—FÖÒ3°Ð Ð¢„–6öâÒ„„”4ôâ”ÆöD–ÖvR„g„vWD–ç7Fæ6T†æFÆR‚’ÂÔ´T”åE$U4õU$4R„”E%õD%õ5Dõ’Â”ÔtUô”4ôâÂÂÂÅ%ôDTdTÅE4•¤R“°Ð¢Õ÷F6¶&$Æ—7BÓå6WE&öw&W757FFR†Õö…væBÂD%eôäõ$ôu$U52“°Ð¢ÒVÇ6R–b†•Æ•7FFRÓÒ5õU4R’°Ð¢'WGFöç5³ÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð¢'WGFöç5³%ÒæGtfÆw2ÒD„$eôTä$ÄTC°Ð¢'WGFöç5³%Òæ”&—FÖÒ3°Ð Ð¢„–6öâÒ„„”4ôâ”ÆöD–ÖvR„g„vWD–ç7Fæ6T†æFÆR‚’ÂÔ´T”åE$U4õU$4R„”E%õD%õU4R’Â”ÔtUô”4ôâÂÂÂÅ%ôDTdTÅE4•¤R“°Ð¢Õ÷F6¶&$Æ—7BÓå6WE&öw&W757FFR†Õö…væBÂÕ÷væE6VV´&"ä†4GW&F–öâ‚’òD%eõU4TB¢D%eôäõ$ôu$U52“°Ð¢ÐÐ Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôEdBbbÕö”EdDFöÖ–âÒEdEôDôÔ”åõF—FÆR’°Ð¢'WGFöç5³ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢'WGFöç5³ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢'WGFöç5³%ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢'WGFöç5³5ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢ÐÐ Ð¢Õ÷F6¶&$Æ—7BÓå6WD÷fW&Æ”–6öâ†Õö…væBÂ„–6öâÂÂ""“°Ð Ð¢–b†„–6öâÒçVÆÇG"’°Ð¢FW7G&÷”–6öâ†„–6öâ“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢f÷"‡6—¦U÷B’Ò²’Âö6÷VçFöb†'WGFöç2“²’²²’°Ð¢'WGFöç5¶•ÒæGtfÆw2ÒD„$eôD•4$ÄTC°Ð¢ÐÐ Ð¢Õ÷F6¶&$Æ—7BÓå6WD÷fW&Æ”–6öâ†Õö…væBÂçVÆÇG"ÂÂ""“°Ð¢Õ÷F6¶&$Æ—7BÓå6WE&öw&W757FFR†Õö…væBÂD%eôäõ$ôu$U52“°Ð¢ÐÐ Ð¢WFFUF‡VÖ&æ–Ä6Æ—‚“°Ð¢ÐÐ Ð¢òòG'’FòÆö6FRF†Rv–æF÷rW6VBFòF—7Æ’F†RF6²&"Fò6†V6²–b—B—2%DÆV@Ð¢–b„5væB¢F6´&%væBÒf–æEv–æF÷r…õB‚%F6´Æ—7EF‡VÖ&æ–ÅvæB"’ÂçVÆÇG"’’°Ð¢òòvRFöâwBvçBF†R'WGFöç2Fò&RÖ—'&÷&VB6òvR&RÖÖ—'&÷"F†VÐÐ¢–b‡F6´&%væBÓävWDW…7G–ÆR‚’bu5ôU…ôÄ”õUE%DÂ’°Ð¢f÷"…T”åB’Ò²’Âö6÷VçFöb†'WGFöç2“²’²²’°Ð¢'WGFöç5¶•Òæ”&—FÖÒö6÷VçFöb†'WGFöç2’Ò'WGFöç5¶•Òæ”&—FÖ°Ð¢ÐÐ¢7FC£§&WfW'6R†'WGFöç2Â'WGFöç2²ö6÷VçFöb†'WGFöç2’“°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&âÕ÷F6¶&$Æ—7BÓåF‡VÖ$&%WFFT'WGFöç2†Õö…væBÂö6÷VçFöb†'WGFöç2’Â'WGFöç2“°Ð§ÐÐ Ð¤…$U5TÅB4Ö–äg&ÖS£¥WFFUF‡VÖ&æ–Ä6Æ—‚Ð§°Ð¢–b‚Õ÷F6¶&$Æ—7BÇÂÕö…væBÇÂÕ÷væEf–WræÕö…væB’°Ð¢&WGW&âUôd”Ã°Ð¢ÐÐ Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð Ð¢5&V7B#°Ð¢Õ÷væEf–WrävWD6Æ–VçE&V7B‚g"“°Ð¢–b‡2æT6F–öäÖVçTÖöFRÓÒÔôDUõ4„õt4D”ôäÔTåR’°Ð¢"äöfg6WE&V7BƒÂvWE7—7FVÔÖWG&–72…4Õô5”ÔTåR’“°Ð¢ÐÐ Ð¢–b‚2æ%W6TVæ†æ6VEF6´&"ÇÂ„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB’ÇÂ—4gVÆÅ67&VVäÖöFR‚’ÇÂ"åv–GF‚‚’ÃÒÇÂ"ä†V–v‡B‚’ÃÒ’°Ð¢&WGW&âÕ÷F6¶&$Æ—7BÓå6WEF‡VÖ&æ–Ä6Æ—†Õö…væBÂçVÆÇG"“°Ð¢ÐÐ Ð¢&WGW&âÕ÷F6¶&$Æ—7BÓå6WEF‡VÖ&æ–Ä6Æ—†Õö…væBÂg"“°Ð§ÐÐ Ð¤$ôôÂ4Ö–äg&ÖS£¤7&VFR„Å5E5E"Ç7¤6Æ74æÖRÂÅ5E5E"Ç7¥v–æF÷tæÖRÂEtõ$BGu7G–ÆRÂ6öç7B$T5Bb&V7BÂ5væB¢&VçEvæBÂÅ5E5E"Ç7¤ÖVçTæÖRÂEtõ$BGtW…7G–ÆRÂ47&VFT6öçFW‡B¢6öçFW‡BÐ§°Ð¢–b†FVfVÇDÕ5F†VÖTÖVçRÓÒçVÆÇG"’°Ð¢FVfVÇDÕ5F†VÖTÖVçRÒDT%TuôäUr4Õ5F†VÖTÖVçR‚“°Ð¢ÐÐ¢–b†Ç7¤ÖVçTæÖRÒåTÄÂ’°Ð¢FVfVÇDÕ5F†VÖTÖVçRÓäÆöDÖVçR†Ç7¤ÖVçTæÖR“°Ð Ð¢–b‚7&VFTW‚†GtW…7G–ÆRÂÇ7¤6Æ74æÖRÂÇ7¥v–æF÷tæÖRÂGu7G–ÆRÀÐ¢&V7BæÆVgBÂ&V7BçF÷Â&V7Bç&–v‡BÒ&V7BæÆVgBÂ&V7Bæ&÷GFöÒÒ&V7BçF÷Â&VçEvæBÓävWE6fT‡væB‚’ÂFVfVÇDÕ5F†VÖTÖVçRÓæÕö„ÖVçRÂ„Ådô”B—6öçFW‡B’’°Ð¢&WGW&âdÅ4S°Ð¢ÐÐ¢FVfVÇDÕ5F†VÖTÖVçRÓægVÆf–ÆÅF†VÖU&W2‡G'VR“°Ð Ð¢&WGW&âE%TS°Ð¢ÐÐ¢&WGW&âdÅ4S°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¦Væ&ÆTf–ÆTF–Æöt†öö²„4Õ5F†VÖUWF–Â¢†VÇW"’°Ð¢–b„g„vWD6WGF–æw2‚’æ%v–æF÷w3F&µF†VÖT7F—fR’²òö†&B6öFVB&V†f–÷"f÷"v–æF÷w2F&²F†VÖRf–ÆRF–Æöw2Â—'&W76V7F—fRöbF†VÖRÆöFVB'’W6W"†f—†–ærv–æF÷w2'Vw2Ð¢vF6†–ætF–ÆörÒF†VÖ&ÆTF–ÆöuG—W3£§v–æF÷w4f–ÆTF–Æös°Ð¢F–Æöt†öö´†VÇW"Ò†VÇW#°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¦Væ&ÆTF–Æöt†öö²„4Õ5F†VÖUWF–Â¢†VÇW"ÂF†VÖ&ÆTF–ÆöuG—W2G—R’°Ð¢–b„—5F†VÖTÆöFVB‚’’°Ð¢vF6†–ætF–ÆörÒG—S°Ð¢F–Æöt†öö´†VÇW"Ò†VÇW#°Ð¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¦—56fU¦öæR„5ö–çBB’°Ð¢5&V7B#°Ð¢Õ÷væE6VV´&"ävWD6Æ–VçE&V7B‡"“°Ð¢Õ÷væE6VV´&"äÖv–æF÷uö–çG2‡F†—2Â"“°Ð¢"ä–æfÆFU&V7BƒÂÕöG’å66ÆU’ƒb’“°Ð¢–b‡"çF÷Â’"çF÷Ò°Ð Ð¢–b‡"åD–å&V7B‡B’’°Ð¢E$4R…õB‚$6Æ–6²v2–ç6–FR6fW¦öæRÆâ"’“°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¥v–æF÷u&ö2…T”åBÖW76vRÂu$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢–b‚Õö…væB’°Ð¢54U%B†fÇ6R“°Ð¢&WGW&â°Ð¢ÐÐ Ð¢–b†ÖW76vRÓÒtÕôÕ5ôõTä5U%Ä”Ä•5Bbb„g„vWD×”‚’ÓæÕöd6Æ÷6–æu7FFRÇÂÕôöä6Æ÷6Uö6ÆÆVBÇÂ—57FFT6Æ÷6–æt&÷'F–ær‚’’’°Ð¢òòF†—26âf÷"W†×ÆR†Vâv†VâÖöFÂF–Æör—26†÷vâGW&–ærÖVF–6Æ÷6RÂ2F†B'Vç2æ÷F†W"ÖW76vRÆö÷ Ð¢E$4R…õB‚$G&÷VBv–æF÷u&ö3¢ÖW76vR‚W‚fÇVRVEÆâ"’ÂÖW76vRÂÄõtõ$B‡u&Ò’“°Ð¢&WGW&â°Ð¢ÐÐ Ð¢6–fFVbDT%TpÐ¢–b†ÖW76vRÒtÕôTåDU$”DÄRbbÖW76vRÒtÕôE$t•DTÒbb—57FFT6Æ÷6–æt&÷'F–ær‚’’°Ð¢E$4R…õB‚%v–æF÷u&ö2GW&–ærÖVF–6Æ÷6S¢ÖW76vR‚W‚fÇVRVEÆâ"’ÂÖW76vRÂÄõtõ$B‡u&Ò’“°Ð¢ÐÐ¢6VæF–`Ð Ð¢–b†ÖW76vRÓÒtÕô5D•dDRÇÂÖW76vRÓÒtÕõ4UDdô5U2ÇÂÖW76vRÓÒtÕôtUDÔ”äÔ„”ädò’°Ð¢–b„g„vWD×”‚’ÓæÕöd6Æ÷6–æu7FFR’°Ð¢E$4R…õB‚$G&÷VBv–æF÷u&ö3¢ÖW76vR‚W‚fÇVRVEÆâ"’ÂÖW76vRÂÄõtõ$B‡u&Ò’“°Ð¢&WGW&â°Ð¢ÐÐ¢ÐÐ Ð¢–b†ÖW76vRÓÒtÕõ5•44ôÔÔäB’°Ð¢T”åBä”BÒÄõtõ$B‡u&Ò’b„ddc°Ð¢–b†ä”BÓÒ45ô4Äõ4R’°Ð¢–b‚g„vWD×”‚’ÓæÕöd6Æ÷6–æu7FFRÇÂÕôöä6Æ÷6Uö6ÆÆVB’°Ð¢öä6Æ÷6R‚“°Ð¢ÐÐ¢&WGW&â°Ð¢ÐÐ¢òõE$4R…õB‚%tÕõ5•44ôÔÔäC¢fÇVR‚W…Æâ"’ÂÄõtõ$B‡u&Ò’“°Ð¢ÐÐ Ð¢–b‚†ÖW76vRÓÒtÕô4ôÔÔäB’bb…D„$åô4Ä”4´TBÓÒ„•tõ$B‡u&Ò’’’°Ð¢–çB6öç7BvÔ–BÒÄõtõ$B‡u&Ò“°Ð¢7v—F6‚‡vÔ–B’°Ð¢66R”ED%ô%UEDôã Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õ5Dõ“°Ð¢'&V³°Ð¢66R”ED%ô%UEDôã# Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ•U4R“°Ð¢'&V³°Ð¢66R”ED%ô%UEDôã3 Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”Eôäd”tDUõ4´•$4²“°Ð¢'&V³°Ð¢66R”ED%ô%UEDôãC Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”Eôäd”tDUõ4´•dõ%t$B“°Ð¢'&V³°Ð¢66R”ED%ô%UEDôãS Ð¢t”äDõuÄ4TÔTåBw°Ð¢vWEv–æF÷uÆ6VÖVçB‚gw“°Ð¢–b‡wç6†÷t6ÖBÓÒ5uõ4„õtÔ”ä”Ô•¤TB’°Ð¢6VæDÖW76vR…tÕõ5•44ôÔÔäBÂ45õ$U5Dõ$RÂÓ“°Ð¢ÐÐ¢6WDf÷&Vw&÷VæEv–æF÷r‚“°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”Eõd”UuôeTÄÅ45$TTâ“°Ð¢'&V³°Ð¢FVfVÇC Ð¢'&V³°Ð¢ÐÐ¢&WGW&â°Ð¢ÒVÇ6R–b‡vF6†–ætF–ÆörÒF†VÖ&ÆTF–ÆöuG—W3£¤æöæRbbçVÆÇG"ÒF–Æöt†öö´†VÇW"bbÖW76vRÓÒtÕô5D•dDRbbÄõtõ$B‡u&Ò’ÓÒtô”ä5D•dR’°Ð¢F–Æöt†öö´†VÇW"ÓçF†VÖ&ÆTF–Æöt†æFÆRÒ„…täB–Å&Ó°Ð¢f÷VæDF–ÆörÒvF6†–ætF–Æös°Ð¢vF6†–ætF–ÆörÒF†VÖ&ÆTF–ÆöuG—W3£¤æöæS°Ð¢òö6GW&R'WB&ö6W72ÖW76vRæ÷&ÖÆÇÐ¢ÒVÇ6R–b†ÖW76vRÓÒtÕôtUD”4ôâbbf÷VæDF–ÆörÓÒF†VÖ&ÆTF–ÆöuG—W3£§v–æF÷w4f–ÆTF–ÆörbbçVÆÇG"ÒF–Æöt†öö´†VÇW"bbçVÆÇG"ÒF–Æöt†öö´†VÇW"ÓçF†VÖ&ÆTF–Æöt†æFÆR’°Ð¢F–Æöt†öö´†VÇW"Óç7V$6Æ74f–ÆTF–Æör‡F†—2“°Ð¢f÷VæDF–ÆörÒF†VÖ&ÆTF–ÆöuG—W3£¤æöæS°Ð¢ÐÐ Ð¢–b†ÖW76vRÓÒtÕôä4Ä%UEDôäDõtâbbu&ÒÓÒ…D4D”ôâbbÕ÷Õe%5"’°Ð¢5ö–çBBÒ5ö–çB„tUEõ…ôÅ$Ò†Å&Ò’ÂtUEõ•ôÅ$Ò†Å&Ò’“°Ð¢67&VVåFô6Æ–VçB‚gB“°Ð¢–b†—56fU¦öæR‡B’’°Ð¢&WGW&â°Ð¢ÐÐ¢ÐÐ Ð¢Å$U5TÅB&WBÒ°Ð¢&ööÂ$6ÆÄ÷W%&ö2ÒG'VS°Ð¢–b†Õ÷Õe%5"’°Ð¢òò6ÆÂÖEe"v–æF÷r&ö2F—&V7FÇ’v†VâF†R–çFW&f6R—2f–Æ&ÆPÐ¢7v—F6‚†ÖW76vR’°Ð¢66RtÕô4Äõ4S Ð¢66RtÕõ5•44ôÔÔäC Ð¢'&V³°Ð¢66RtÕôÔõU4TÔõdS Ð¢66RtÕôÄ%UEDôäDõtã Ð¢66RtÕôÄ%UEDôåU Ð¢òò4Ö÷W6UvæBv–ÆÂ6ÆÂÖEe"v–æF÷r&ö0Ð¢'&V³°Ð¢FVfVÇC Ð¢$6ÆÄ÷W%&ö2ÒÕ÷Õe%5"Óå&VçEv–æF÷u&ö2†Õö…væBÂÖW76vRÂgu&ÒÂfÅ&ÒÂg&WB“°Ð¢ÐÐ¢ÐÐ¢–b†$6ÆÄ÷W%&ö2bbÕö…væB’°Ð¢&WBÒõ÷7WW#£¥v–æF÷u&ö2†ÖW76vRÂu&ÒÂÅ&Ò“°Ð¢ÐÐ Ð¢&WGW&â&WC°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤—4W&õ6æVB‚Ð§°Ð¢&ööÂ&WBÒfÇ6S°Ð¢t”äDõuÄ4TÔTåBwÒ²6—¦Vöb‡w’Ó°Ð¢–b„—5v–æF÷uf—6–&ÆR‚’bb—5¦ööÖVB‚’bb—4–6öæ–2‚’bbvWEv–æF÷uÆ6VÖVçB‚gw’’°Ð¢5&V7B&V7C°Ð¢vWEv–æF÷u&V7B‡&V7B“°Ð¢–b„„Ôôä•Dõ"„ÖöâÒÖöæ—F÷$g&öÕ&V7B‡&V7BÂÔôä•Dõ%ôDTdTÅEDôåTÄÂ’’°Ð¢Ôôä•Dõ$”ädòÖ’Ò²6—¦Vöb†Ö’’Ó°Ð¢–b„vWDÖöæ—F÷$–æfò†„ÖöâÂfÖ’’’°Ð¢5&V7Bw&V7B‡wç&4æ÷&ÖÅ÷6—F–öâ“°Ð¢w&V7Bäöfg6WE&V7B†Ö’ç&5v÷&²æÆVgBÒÖ’ç&4Ööæ—F÷"æÆVgBÂÖ’ç&5v÷&²çF÷ÒÖ’ç&4Ööæ—F÷"çF÷“°Ð¢&WBÒ‡&V7BÒw&V7B“°Ð¢ÒVÇ6R°Ð¢54U%B„dÅ4R“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢&WGW&â&WC°Ð§ÐÐ Ð¥T”åB4Ö–äg&ÖS£¤öå÷vW$'&öF67B…T”åBå÷vW$WfVçBÂÅ$ÒäWfVçDFFÐ§°Ð¢7FF–2$ôôÂ%v5W6VD&Vf÷&U7W7VçF–öâÒdÅ4S°Ð Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤öå÷vW$'&öF67B‚WR’"’Âå÷vW$WfVçB“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ Ð¢7v—F6‚†å÷vW$WfVçB’°Ð¢66R%EôÕ5U5TäC¢òò7—7FVÒ—27W7VæF–ær÷W&F–öâàÐ¢66R%EôÕ5DäD%“ Ð¢E$4R…õB‚$öå÷vW$'&öF67BÒ7W7VæF–æuÆâ"’“°Ð¢%v5W6VD&Vf÷&U7W7VçF–öâÒdÅ4S² Ð Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTB’°Ð¢–b„g„vWD6WGF–æw2‚’æ•&VÆöDgFW$ÆöæuW6RãÒ’°Ð¢òò6fR÷6—F–öâæB6Æ÷6PÐ¢Õ÷&VÆöDf–ÆVæÖRÒÆ7D÷Väf–ÆS°Ð¢Õ÷'E&VÆöE÷2ÒÕ÷væE6VV´&"ä†4GW&F–öâ‚’òÕ÷væE6VV´&"ävWE÷2‚’¢°Ð¢&VÆöD%&WVBÒ%&WVC°Ð¢Õö•&VÆöDVF–ô–G‚ÒvWD7W'&VçDVF–õG&6´–G‚‚“°Ð¢Õö•&VÆöE7V$–G‚ÒvWD7W'&VçE7V'F—FÆUG&6´–G‚‚“°Ð¢ÕöGtÆ7EW6RÒTÄÃ²òòW6VB2†–&W&æF–öâ6–væÀÐ¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”Eôd”ÄUô4Äõ4TÔTD”“°Ð¢ÒVÇ6R–b„vWDÖVF–7FFTF—&V7B‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢%v5W6VD&Vf÷&U7W7VçF–öâÒE%TS°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢ÐÐ¢ÒVÇ6R–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôD”är’°Ð¢ÕöGtÆ7EW6RÒTÄÃ²òòW6VB2†–&W&æF–öâ6–væÀÐ¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”Eôd”ÄUô4Äõ4TÔTD”“°Ð¢ÐÐ¢'&V³°Ð¢66R%EôÕ$U5TÔU5U5TäC¢òò7—7FVÒ—2&W7VÖ–ær÷W&F–öàÐ¢66R%EôÕ$U5TÔU5DäD%“ Ð¢E$4R…õB‚$öå÷vW$'&öF67BÒ&W7VÖ–æuÆâ"’“°Ð Ð¢–b‡2æä4Å7v—F6†W2b4Å5uô4Äõ4R’°Ð¢÷7DÖW76vR…tÕô4Äõ4R“°Ð¢ÒVÇ6R°Ð¢òò&W7VÖR–bvRW6VB&Vf÷&R7W7Vç6–öâàÐ¢–b†%v5W6VD&Vf÷&U7W7VçF–öâ’°Ð¢÷7DÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ’“°Ð¢ÐÐ¢ÐÐ¢'&V³°Ð¢ÐÐ Ð¢&WGW&âõ÷7WW#£¤öå÷vW$'&öF67B†å÷vW$WfVçBÂäWfVçDFF“°Ð§ÐÐ Ð¢6FVf–æRäõD”e•ôdõ%õD„•5õ4U54”ôâ Ð Ð§fö–B4Ö–äg&ÖS£¤öå6W76–öä6†ævR…T”åBå6W76–öå7FFRÂT”åBä–BÐ§°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b…U4UôÄôttU"‡2’’°Ð¢Ä”U%ôÄôr…õB‚$4Ö–äg&ÖS£¤öå6W76–öä6†ævR‚WR’"’Âå6W76–öå7FFR“°Ð¢dÅU4…ôÄôttU"‚“°Ð¢ÐÐ Ð¢–b‡2æ$Æö6´æõW6R’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢7FF–2$ôôÂ%v5W6VD&Vf÷&U6W76–öä6†ævRÒdÅ4S°Ð Ð¢7v—F6‚†å6W76–öå7FFR’°Ð¢66RuE5õ4U54”ôåôÄô4³ Ð¢E$4R…õB‚$öå6W76–öä6†ævRÒÆö6²6W76–öåÆâ"’“°Ð¢%v5W6VD&Vf÷&U6W76–öä6†ævRÒdÅ4S°Ð Ð¢–b„vWDÖVF–7FFTF—&V7B‚’ÓÒ7FFUõ'Vææ–ærbbÕödVF–ôöæÇ’’°Ð¢%v5W6VD&Vf÷&U6W76–öä6†ævRÒE%TS°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õU4R“°Ð¢ÐÐ¢'&V³°Ð¢66RuE5õ4U54”ôåõTäÄô4³ Ð¢E$4R…õB‚$öå6W76–öä6†ævRÒVäÆö6²6W76–öåÆâ"’“°Ð Ð¢–b†%v5W6VD&Vf÷&U6W76–öä6†ævR’°Ð¢6VæDÖW76vR…tÕô4ôÔÔäBÂ”EõÄ•õÄ’“°Ð¢ÐÐ¢'&V³°Ð¢FVfVÇC Ð¢E$4R…õB‚$öå6W76–öä6†ævRÒWUÆâ"’Âå6W76–öå7FFR“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥uE5&Vv—7FW%6W76–öäæ÷F–f–6F–öâ‚Ð§°Ð¢6öç7Bv–æ”gVæ3Ä$ôôÂt”ä’„…täBÂEtõ$B“àÐ¢fåwG5&Vv—7FW%6W76–öäæ÷F–f–6F–öâÒ²õB‚'wG6“3"æFÆÂ"’Â%uE5&Vv—7FW%6W76–öäæ÷F–f–6F–öâ"Ó°Ð Ð¢–b†fåwG5&Vv—7FW%6W76–öäæ÷F–f–6F–öâ’°Ð¢fåwG5&Vv—7FW%6W76–öäæ÷F–f–6F–öâ†Õö…væBÂäõD”e•ôdõ%õD„•5õ4U54”ôâ“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥uE5Vå&Vv—7FW%6W76–öäæ÷F–f–6F–öâ‚Ð§°Ð¢6öç7Bv–æ”gVæ3Ä$ôôÂt”ä’„…täB“àÐ¢fåwG5Vå&Vv—7FW%6W76–öäæ÷F–f–6F–öâÒ²õB‚'wG6“3"æFÆÂ"’Â%uE5Vå&Vv—7FW%6W76–öäæ÷F–f–6F–öâ"Ó°Ð Ð¢–b†fåwG5Vå&Vv—7FW%6W76–öäæ÷F–f–6F–öâ’°Ð¢fåwG5Vå&Vv—7FW%6W76–öäæ÷F–f–6F–öâ†Õö…væB“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFU6VV¶&$6†FW$&r‚Ð§°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b‡2æe6†÷t6†FW'2bbÕ÷4"bbÕ÷4"Óä6†vWD6÷VçB‚’â’°Ð¢Õ÷væE6VV´&"å6WD6†FW$&r†Õ÷4"“°Ð¢Õôõ4Bå6WD6†FW$&r†Õ÷4"“°Ð¢ÒVÇ6R°Ð¢Õ÷væE6VV´&"å&VÖ÷fT6†FW'2‚“°Ð¢Õôõ4Bå&VÖ÷fT6†FW'2‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFTVF–õ7v—F6†W"‚Ð§°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢46öÕ•G#Ä”VF–õ7v—F6†W$f–ÇFW#â4bÒf–æDf–ÇFW"…õ÷WV–Föb„4VF–õ7v—F6†W$f–ÇFW"’ÂÕ÷t"“°Ð Ð¢–b‡4b’°Ð¢4bÓå6WE7V¶W$6öæf–r‡2æd7W7FöÔ6†ææVÄÖ–ærÂ2ç7V¶W%Fô6†ææVÄÖ“°Ð¢4bÓå6WDVF–õF–ÖU6†–gB‡2ædVF–õF–ÖU6†–gBò“cB¢2æ”VF–õF–ÖU6†–gB¢“°Ð¢4bÓå6WDæ÷&ÖÆ—¦T&ö÷7C"‡2ædVF–ôæ÷&ÖÆ—¦RÂ2æäVF–ôÖ„æ÷&Ôf7F÷"Â2ædVF–ôæ÷&ÖÆ—¦U&V6÷fW"Â2æäVF–ô&ö÷7B“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÆöD'EFõf–Ww2†6öç7B57G&–ærb–ÖvUF‚Ð§°Ð¢Õ÷væEf–WräÆöD–Ör†–ÖvUF‚“°Ð¢–b„†4FVF–6FVDe5f–FVõv–æF÷r‚’’°Ð¢Õ÷FVF–6FVDe5f–FVõvæBÓäÆöD–Ör†–ÖvUF‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÆöD'EFõf–Ww2‡7FC£§fV7F÷#Ä%•DSâ'VffW"Ð§°Ð¢Õ÷væEf–WräÆöD–Ör†'VffW"“°Ð¢–b„†4FVF–6FVDe5f–FVõv–æF÷r‚’’°Ð¢Õ÷FVF–6FVDe5f–FVõvæBÓäÆöD–Ör†'VffW"“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤6ÆV$'Dg&öÕf–Ww2‚Ð§°Ð¢Õ÷væEf–WräÆöD–Ör‚“°Ð¢–b„†4FVF–6FVDe5f–FVõv–æF÷r‚’’°Ð¢Õ÷FVF–6FVDe5f–FVõvæBÓäÆöD–Ör‚“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFT6öçG&öÅ7FFR…WFFT6öçG&öÅF&vWBF&vWBÐ§°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢7v—F6‚‡F&vWB’°Ð¢66RUDDUõdôÅTÔUõ5DU Ð¢Õ÷væEFööÄ&"æÕ÷föÆ7G&Âå6WEvU6—¦R‡2æåföÇVÖU7FW“°Ð¢'&V³°Ð¢66RUDDUôÄôtó Ð¢–b‚Õ÷væEf–Wrä—47W7FöÔ–ÖtÆöFVB‚’’°Ð¢6ÆV$'Dg&öÕf–Ww2‚“°Ð¢ÐÐ¢'&V³°Ð¢66RUDDUôÔTD”ô%C Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbbÕödVF–ôöæÇ’bb2æ$Væ&ÆT6÷fW$'B’°Ð¢57G&–ærf–ÆVæÖRÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‚“°Ð¢57G&–ærf–ÆVæÖUöæõöW‡C°Ð¢57G&–ærf–ÆVF—#°Ð¢–b‚F…WF–Ç3£¤—5U$Â†f–ÆVæÖR’’°Ð¢5F‚F‚Ò5F‚†f–ÆVæÖR“°Ð¢–b‡F‚äf–ÆTW†—7G2‚’’°Ð¢F‚å&VÖ÷fTW‡FVç6–öâ‚“°Ð¢f–ÆVæÖUöæõöW‡BÒF‚æÕ÷7G%Fƒ°Ð¢F‚å&VÖ÷fTf–ÆU7V2‚“°Ð¢f–ÆVF—"ÒF‚æÕ÷7G%Fƒ°Ð¢ÐÐ¢ÐÐ Ð¢57G&–ærWF†÷#°Ð¢Õ÷væD–æfô&"ävWDÆ–æR…7G%&W2„”E5ô”ädô$%ôUD„õ"’ÂWF†÷"“°Ð Ð¢46öÕ•G#Ä”f–ÇFW$w&ƒâf–ÇFW$w&‚ÒÕ÷t#°Ð¢7FC£§fV7F÷#Ä%•DSâ–çFW&æÄ6÷fW#°Ð¢–b„6÷fW$'C£¤f–æDVÖ&VFFVB‡f–ÇFW$w&‚Â–çFW&æÄ6÷fW"’’°Ð¢ÆöD'EFõf–Ww2†–çFW&æÄ6÷fW"“°Ð¢Õö7W'&VçD6÷fW%F‚Òf–ÆVæÖS°Ð¢Õö7W'&VçD6÷fW$WF†÷"ÒWF†÷#°Ð¢ÒVÇ6R°Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’bbÆ’æÕö6÷fW"ä—4V×G’‚’bb5F‚‡Æ’æÕö6÷fW"’äf–ÆTW†—7G2‚’’°Ð¢ÆöD'EFõf–Ww2‡Æ’æÕö6÷fW"“°Ð¢ÒVÇ6R–b…F…WF–Ç3£¤—5U$Â†f–ÆVæÖR’’°Ð¢6ÆV$'Dg&öÕf–Ww2‚“°Ð¢ÒVÇ6R–b‚f–ÆVF—"ä—4V×G’‚’bb†Õö7W'&VçD6÷fW%F‚Òf–ÆVF—"ÇÂÕö7W'&VçD6÷fW$WF†÷"ÒWF†÷"ÇÂ7W'&VçD6÷fW$—4f–ÆT'B’’°Ð¢57G&–ær–ÖrÒ6÷fW$'C£¤f–æDW‡FW&æÂ†f–ÆVæÖUöæõöW‡BÂf–ÆVF—"ÂWF†÷"Â7W'&VçD6÷fW$—4f–ÆT'B“°Ð¢ÆöD'EFõf–Ww2†–Ör“°Ð¢–b†–Örä—4V×G’‚’’°Ð¢Õö7W'&VçD6÷fW%F‚äV×G’‚“°Ð¢Õö7W'&VçD6÷fW$WF†÷"äV×G’‚“°Ð¢ÒVÇ6R°Ð¢Õö7W'&VçD6÷fW%F‚Òf–ÆVF—#°Ð¢Õö7W'&VçD6÷fW$WF†÷"ÒWF†÷#°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢Õö7W'&VçD6÷fW%F‚äV×G’‚“°Ð¢Õö7W'&VçD6÷fW$WF†÷"äV×G’‚“°Ð¢6ÆV$'Dg&öÕf–Ww2‚“°Ð¢ÐÐ¢'&V³°Ð¢66RUDDUõ4TT´$%ô4„DU%3 Ð¢WFFU6VV¶&$6†FW$&r‚“°Ð¢'&V³°Ð¢66RUDDUõt”äDõuõD•DÄS Ð¢÷Vå6WGWv–æF÷uF—FÆR‚“°Ð¢'&V³°Ð¢66RUDDUôTD”õõ5t•D4„U# Ð¢WFFTVF–õ7v—F6†W"‚“°Ð¢'&V³°Ð¢66RUDDUô4ôåE$ôÅ5õd•4”$”Ä•E“ Ð¢Õö6öçG&öÇ2åWFFUFööÆ&'5f—6–&–Æ—G’‚“°Ð¢'&V³°Ð¢66RUDDUô4„”ÄEd”Uuô5U%4õ%ô„4³ Ð¢òò„4³¢v–æF÷vVB†æ÷B&VæFW&ÆW72’f–FVò&VæFW&W'27&VFVB–âw&‚F‡&VBFòæ÷@Ð¢òò&öGV6RtÕôÔõU4TÔõdRÖW76vRv†VâvR&VÆV6RÖ÷W6R6GW&RöâF÷öb—BÂ†W&Rw2v÷&¶&÷Væ@Ð¢Õ÷F–ÖW$öæUF–ÖRå7V'67&–&R…F–ÖW$öæUF–ÖU7V'67&–&W#£¤4„”ÄEd”Uuô5U%4õ%ô„4²Â7FC£¦&–æB‚d46†–ÆEf–Ws£¤–çfÆ–FFRÂfÕ÷væEf–WrÂdÅ4R’Âb“°Ð¢'&V³°Ð¢FVfVÇC Ð¢54U%B„dÅ4R“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥&VÆöDÖVçW2‚’°Ð¢òò4ÖVçRFVfVÇDÖVçS°Ð¢4ÖVçR¢öÆDÖVçS°Ð Ð¢òòFW7G&÷’F†RG–æÖ–2ÖVçW2&Vf÷&R&VÆöF–ærF†RÖ–âÖVçW0Ð¢FW7G&÷”G–æÖ–4ÖVçW2‚“°Ð Ð¢òò&VÆöBF†RÖ–âÖVçW0Ð¢Õ÷÷WÖVçRäFW7G&÷”ÖVçR‚“°Ð¢Õ÷÷WÖVçRäÆöDÖVçR„”E%õõU“°Ð¢ÕöÖ–å÷WÖVçRäFW7G&÷”ÖVçR‚“°Ð¢ÕöÖ–å÷WÖVçRäÆöDÖVçR„”E%õõUÔ”â“°Ð Ð¢öÆDÖVçRÒvWDÖVçR‚“°Ð¢FVfVÇDÕ5F†VÖTÖVçRÒDT%TuôäUr4Õ5F†VÖTÖVçR‚“²ò÷v–ÆÂ†fR&VVâFW7G&÷–V@Ð¢FVfVÇDÕ5F†VÖTÖVçRÓäÆöDÖVçR„”E%ôÔ”äe$ÔR“°Ð¢–b†öÆDÖVçR’°Ð¢òòGF6‚F†RæWrÖVçRFòF†Rv–æF÷röæÇ’–bF†W&Rv2ÖVçR&Vf÷&PÐ¢6WDÖVçR†FVfVÇDÕ5F†VÖTÖVçR“°Ð¢òòæBF†VâFW7G&÷’F†RöÆBöæPÐ¢öÆDÖVçRÓäFW7G&÷”ÖVçR‚“°Ð¢FVÆWFRöÆDÖVçS°Ð¢ÐÐ¢ò÷vRFöâwBFWF6‚&V6W6RvR&WF–âF†R6ÖVçPÐ¢òöÕö„ÖVçTFVfVÇBÒFVfVÇDÖVçRäFWF6‚‚“°Ð¢Õö„ÖVçTFVfVÇBÒFVfVÇDÕ5F†VÖTÖVçRÓävWE6fT†ÖVçR‚“°Ð Ð¢Õ÷÷WÖVçRægVÆf–ÆÅF†VÖU&W2‚“°Ð¢ÕöÖ–å÷WÖVçRægVÆf–ÆÅF†VÖU&W2‚“°Ð¢FVfVÇDÕ5F†VÖTÖVçRÓægVÆf–ÆÅF†VÖU&W2‡G'VR“°Ð Ð¢òò&VÆöBF†RG–æÖ–2ÖVçW0Ð¢7&VFTG–æÖ–4ÖVçW2‚“°Ð¢ÆöDG–æÖ–4ÖVçW2‚“°Ð§ÐÐ Ð Ð§fö–B4Ö–äg&ÖS£¥WFFUT”ÆæwVvR‚Ð§°Ð¢&VÆöDÖVçW2‚“°Ð Ð¢òò&VÆöBF†R7FF–2&'0Ð¢÷Vå6WGW–æfô&"‚“°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôD”t•DÅô4EU$R’°Ð¢WFFT7W'&VçD6†ææVÄ–æfò†fÇ6RÂfÇ6R“°Ð¢ÐÐ¢÷Vå6WGW7FG4&"‚“°Ð Ð¢òò&VÆöBF†RFV'Vr6†FW'2F–Æör–bæVVB&PÐ¢–b†Õ÷FV'Vu6†FW'2bb—5v–æF÷r†Õ÷FV'Vu6†FW'2ÓæÕö…væB’’°Ð¢$ôôÂ%v5f—6–&ÆRÒÕ÷FV'Vu6†FW'2Óä—5v–æF÷uf—6–&ÆR‚“°Ð¢dU$”e’†Õ÷FV'Vu6†FW'2ÓäFW7G&÷•v–æF÷r‚’“°Ð¢Õ÷FV'Vu6†FW'2Ò7FC£¦Ö¶U÷Væ—VSÄ4FV'Vu6†FW'4FÆsâ‚“°Ð¢–b†%v5f—6–&ÆR’°Ð¢Õ÷FV'Vu6†FW'2Óå6†÷uv–æF÷r…5uõ4„õtä“°Ð¢òòFöâwB7FVÂfö7W2g&öÒÖ–âg&ÖPÐ¢6WD7F—fUv–æF÷r‚“°Ð¢ÐÐ¢ÐÐ Ð¢òò&VÆöBF†R6öÆ÷"6öçG&öÇ2F–Æör–bæVVB&PÐ¢–b†Õ÷6öÆ÷$6öçG&öÇ2bb—5v–æF÷r†Õ÷6öÆ÷$6öçG&öÇ2ÓæÕö…væB’’°Ð¢$ôôÂ%v5f—6–&ÆRÒÕ÷6öÆ÷$6öçG&öÇ2Óä—5v–æF÷uf—6–&ÆR‚“°Ð¢dU$”e’†Õ÷6öÆ÷$6öçG&öÇ2ÓäFW7G&÷•v–æF÷r‚’“°Ð¢Õ÷6öÆ÷$6öçG&öÇ2Ò7FC£¦Ö¶U÷Væ—VSÄ46öÆ÷$6öçG&öÇ4FÆsâ‚“°Ð¢–b†%v5f—6–&ÆR’°Ð¢Õ÷6öÆ÷$6öçG&öÇ2Óå6†÷uv–æF÷r…5uõ4„õtä“°Ð¢òòFöâwB7FVÂfö7W2g&öÒÖ–âg&ÖPÐ¢6WD7F—fUv–æF÷r‚“°Ð¢ÐÐ¢ÐÐ§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤÷Vä$B„57G&–ærF‚Ð§°Ð¢4†F×d6Æ—–æfò6Æ—–æfó°Ð¢57G&–ær7G%Æ–Æ—7Df–ÆS°Ð¢4†F×d6Æ—–æfó£¤†F×eÆ–Æ—7BÖ–åÆ–Æ—7C°Ð Ð¢6–b”åDU$äÅõ4õU$4Td”ÅDU%ôÕTpÐ¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢&ööÂ–çFW&æÄ×Vu7Æ—GFW"Ò2å7&4f–ÇFW'5µ5$5ôÕTuÒÇÂ2å7&4f–ÇFW'5µ5$5ôÕTuE5Ó°Ð¢6VÇ6PÐ¢&ööÂ–çFW&æÄ×Vu7Æ—GFW"ÒfÇ6S°Ð¢6VæF–`Ð Ð¢ÕôÆ7D÷Vä$EF‚ÒFƒ°Ð Ð¢57G&–ærW‡BÒ5F‚…F‚’ävWDW‡FVç6–öâ‚“°Ð¢W‡BäÖ¶TÆ÷vW"‚“°Ð Ð¢–b‚„5F‚…F‚’ä—4F—&V7F÷'’‚’bbF‚äf–æB…õB‚%ÅÄ$DÕb"’’’ÇÂ5F‚…F‚²õB‚%ÅÄ$DÕb"’’ä—4F—&V7F÷'’‚’ÇÂ‚W‡Bä—4V×G’‚’bbW‡BÓÒõB‚"æ&F×b"’’’°Ð¢–b‚W‡Bä—4V×G’‚’bbW‡BÓÒõB‚"æ&F×b"’’°Ð¢F‚å&WÆ6R…õB‚%ÅÄ$DÕeÅÂ"’ÂõB‚%ÅÂ"’“°Ð¢5F‚õF‚…F‚“°Ð¢õF‚å&VÖ÷fTf–ÆU7V2‚“°Ð¢F‚Ò57G&–ær…õF‚“°Ð¢ÒVÇ6R–b…F‚äf–æB…õB‚%ÅÄ$DÕb"’’’°Ð¢F‚å&WÆ6R…õB‚%ÅÄ$DÕb"’ÂõB‚%ÅÂ"’“°Ð¢ÐÐ¢–b…5T44TTDTB„6Æ—–æfòäf–æDÖ–äÖ÷f–R…F‚Â7G%Æ–Æ—7Df–ÆRÂÖ–åÆ–Æ—7BÂÕôÕÅ5Æ–Æ—7B’’’°Ð¢Õö$—4$EÆ’ÒG'VS°Ð Ð¢Õö$†4$DÖWFÒ6Æ—–æfòå&VDÖWF…F‚ÂÕô$DÖWF“°Ð Ð¢–b‚–çFW&æÄ×Vu7Æ—GFW"bbW‡Bä—4V×G’‚’bbW‡BÓÒõB‚"æ&F×b"’’°Ð¢&WGW&âfÇ6S°Ð¢ÒVÇ6R°Ð¢Õ÷væEÆ–Æ—7D&"äV×G’‚“°Ð¢4FÄÆ—7CÄ57G&–æsâ6Ã°Ð Ð¢–b„–çFW&æÄ×Vu7Æ—GFW"’°Ð¢6ÂäFEF–Â„57G&–ær‡7G%Æ–Æ—7Df–ÆR’“°Ð¢ÒVÇ6R°Ð¢6ÂäFEF–Â„57G&–ær…F‚²õB‚%ÅÄ$DÕeÅÆ–æFW‚æ&F×b"’’“°Ð¢ÐÐ Ð¢Õ÷væEÆ–Æ—7D&"äVæB‡6ÂÂfÇ6R“°Ð¢÷7DÖW76vR…tÕôÕ5ôõTä5U%Ä”Ä•5BÂÂ“°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢ÕôÆ7D÷Vä$EF‚ÒõB‚""“°Ð¢&WGW&âfÇ6S°Ð§ÐÐ Ð¢òò&WGW&ç2F†RF†R6÷'&W7öæF–ær7V$–çWB÷"çVÆÇG"–â66RöbW'&÷"àÐ¢òò’—2ÖöF–f–VBFò&VfÆV7BF†RÆö6ÆR–æFW‚öbG&6°Ð¥7V'F—FÆT–çWB¢4Ö–äg&ÖS£¤vWE7V'F—FÆT–çWB†–çBb’Â&ööÂ$—4öfg6WBò£ÒfÇ6R¢òÐ§°Ð¢òòöæÇ’ÂæBÓ&R7W÷'FVBöfg6WG0Ð¢–b‚†$—4öfg6WBbb†’ÂÓÇÂ’â’’ÇÂ‚$—4öfg6WBbb’Â’’°Ð¢&WGW&âçVÆÇG#°Ð¢ÐÐ Ð¢õ4•D”ôâ÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢7V'F—FÆT–çWB¢7V$–çWBÒçVÆÇG"Â§7V$–çWE&V2ÒçVÆÇG#°Ð¢–çB”Æö6Ä–G‚ÒÓÂ”Æö6Ä–G…&V2ÒÓ°Ð¢&ööÂ$æW‡EG&6²ÒfÇ6S°Ð Ð¢v†–ÆR‡÷2bb7V$–çWB’°Ð¢7V'F—FÆT–çWBb7V$–çWBÒÕ÷7V%7G&V×2ävWDæW‡B‡÷2“°Ð Ð¢–b„46öÕ•G#Ä”Õ7G&VÕ6VÆV7Câ54bÒ7V$–çWBç6÷W&6Tf–ÇFW"’°Ð¢Etõ$B57G&V×3°Ð¢–b„d”ÄTB‡54bÓä6÷VçB‚f57G&V×2’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢f÷"†–çB¢ÒÂ6çBÒ†–çB–57G&V×3²¢Â6çC²¢²²’°Ð¢Etõ$BGtfÆw2ÂGtw&÷W°Ð Ð¢–b„d”ÄTB‡54bÓä–æfò†¢ÂçVÆÇG"ÂfGtfÆw2ÂçVÆÇG"ÂfGtw&÷WÂçVÆÇG"ÂçVÆÇG"ÂçVÆÇG"’’’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†Gtw&÷WÒ"’°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–b†$—4öfg6WB’°Ð¢–b†$æW‡EG&6²’²òòvRFWFV7FVB&Wf–÷W6Ç’F†BF†RæW‡B7V'F—FÆW2G&6²—2F†RöæRvRvçBFò6VÆV7@Ð¢7V$–çWBÒg7V$–çWC°Ð¢”Æö6Ä–G‚Ò£°Ð¢'&V³°Ð¢ÒVÇ6R–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÐÐ¢bbGtfÆw2b„Õ5E$TÕ4TÄT5D”ädõôTä$ÄTBÂÕ5E$TÕ4TÄT5D”ädõôU„4ÅU4•dR’’°Ð¢–b†’ÓÒ’°Ð¢7V$–çWBÒg7V$–çWC°Ð¢”Æö6Ä–G‚Ò£°Ð¢'&V³°Ð¢ÒVÇ6R–b†’â’°Ð¢$æW‡EG&6²ÒG'VS²òòvRvçBFòF†R6VÆV7BF†RæW‡B7V'F—FÆW2G&6°Ð¢ÒVÇ6R°Ð¢òòvRvçBF†R&Wf–÷W27V'F—FÆW2G&6²æBvR¶æ÷rv†–6‚öæR—B—0Ð¢–b‡7V$–çWE&V2’°Ð¢7V$–çWBÒ7V$–çWE&V3°Ð¢”Æö6Ä–G‚Ò”Æö6Ä–G…&V3°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢7V$–çWE&V2Òg7V$–çWC°Ð¢”Æö6Ä–G…&V2Ò£°Ð¢ÒVÇ6R°Ð¢–b†’ÓÒ’°Ð¢7V$–çWBÒg7V$–çWC°Ð¢”Æö6Ä–G‚Ò£°Ð¢'&V³°Ð¢ÐÐ Ð¢’ÒÓ°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢–b†$—4öfg6WB’°Ð¢–b†$æW‡EG&6²’²òòvRFWFV7FVB&Wf–÷W6Ç’F†BF†RæW‡B7V'F—FÆW2G&6²—2F†RöæRvRvçBFò6VÆV7@Ð¢7V$–çWBÒg7V$–çWC°Ð¢”Æö6Ä–G‚Ò°Ð¢'&V³°Ð¢ÒVÇ6R–b‡7V$–çWBç7V%7G&VÒÓÒÕ÷7W'&VçE7V$–çWBç7V%7G&VÒ’°Ð¢”Æö6Ä–G‚Ò7V$–çWBç7V%7G&VÒÓävWE7G&VÒ‚’²“°Ð¢–b†”Æö6Ä–G‚ãÒbb”Æö6Ä–G‚Â7V$–çWBç7V%7G&VÒÓävWE7G&VÔ6÷VçB‚’’°Ð¢òòF†R7V'F—FÆW2G&6²vRvçBFò6VÆV7B—2'BöbF†—27V'7G&VÐÐ¢7V$–çWBÒg7V$–çWC°Ð¢ÒVÇ6R–b†’â’²òòvRvçBFòF†R6VÆV7BF†RæW‡B7V'F—FÆW2G&6°Ð¢$æW‡EG&6²ÒG'VS°Ð¢ÒVÇ6R°Ð¢òòvRvçBF†R&Wf–÷W27V'F—FÆW2G&6²æBvR¶æ÷rv†–6‚öæR—B—0Ð¢–b‡7V$–çWE&V2’°Ð¢7V$–çWBÒ7V$–çWE&V3°Ð¢”Æö6Ä–G‚Ò”Æö6Ä–G…&V3°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢7V$–çWE&V2Òg7V$–çWC°Ð¢”Æö6Ä–G…&V2Ò7V$–çWBç7V%7G&VÒÓävWE7G&VÔ6÷VçB‚’Ò°Ð¢ÐÐ¢ÒVÇ6R°Ð¢–b†’Â7V$–çWBç7V%7G&VÒÓävWE7G&VÔ6÷VçB‚’’°Ð¢7V$–çWBÒg7V$–çWC°Ð¢”Æö6Ä–G‚Ò“°Ð¢ÒVÇ6R°Ð¢’ÓÒ7V$–çWBç7V%7G&VÒÓävWE7G&VÔ6÷VçB‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢òò†æFÆR7V6–Â66W0Ð¢–b‚÷2bb7V$–çWBbb$—4öfg6WB’°Ð¢–b†$æW‡EG&6²’²òòF†RÆ7B7V'F—FÆW2G&6²v26VÆV7FVBæBvRvçBF†RæW‡BöæPÐ¢òòÆWBw2&W7F'BF†RÆö÷Fò6VÆV7BF†Rf—'7B7V'F—FÆW2G&6°Ð¢÷2ÒÕ÷7V%7G&V×2ävWD†VE÷6—F–öâ‚“°Ð¢ÒVÇ6R–b†’Â’²òòF†Rf—'7B7V'F—FÆW2G&6²v26VÆV7FVBæBvRvçBF†R&Wf–÷W2öæPÐ¢7V$–çWBÒ7V$–çWE&V3²òòvR6VÆV7BF†RÆ7BG&6°Ð¢”Æö6Ä–G‚Ò”Æö6Ä–G…&V3°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢’Ò”Æö6Ä–Gƒ°Ð Ð¢&WGW&â7V$–çWC°Ð§ÐÐ Ð¤57G&–ær4Ö–äg&ÖS£¤vWDf–ÆTæÖR‚Ð§°Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’’°Ð¢57G&–ærF‚†Õ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‡G'VR’“°Ð¢–b‚Æ’æÕö%–÷WGV&TDÂbbÕ÷e4b’°Ð¢46öÔ†VG#ÄôÄT4„#âdã°Ð¢–b…5T44TTDTB†Õ÷e4bÓävWD7W$f–ÆR‚gdâÂçVÆÇG"’’’°Ð¢F‚Òdã°Ð¢ÐÐ¢ÐÐ¢–b…F…WF–Ç3£¤—5U$Â‡F‚’’°Ð¢F‚Ò6†÷'FVåU$Â‡F‚“°Ð¢ÐÐ¢&WGW&âÆ’æÕö%–÷WGV&TDÂòF‚¢F…WF–Ç3£¥7G&—F„÷%W&Â‡F‚“°Ð¢ÐÐ¢&WGW&âõB‚""“°Ð§ÐÐ Ð¤57G&–ær4Ö–äg&ÖS£¤vWD6GW&UF—FÆR‚Ð§°Ð¢57G&–ærF—FÆS°Ð Ð¢F—FÆRäÆöE7G&–ær„”E5ô4EU$UôÄ•dR“°Ð¢–b„vWEÆ–&6´ÖöFR‚’ÓÒÕôäÄôuô4EU$R’°Ð¢57G&–ærFWdæÖRÒvWDg&–VæFÇ”æÖR†Õõf–DF—7æÖR“°Ð¢–b‚FWdæÖRä—4V×G’‚’’°Ð¢F—FÆRäVæDf÷&ÖB…õB‚"ÂW2"’ÂFWdæÖRävWE7G&–ær‚’“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢57G&–ærbWfVçDæÖRÒÕ÷Ed%7FFRÓäæ÷tæW‡BæWfVçDæÖS°Ð¢–b†Õ÷Ed%7FFRÓæ$7F—fR’°Ð¢F—FÆRäVæDf÷&ÖB…õB‚"ÂW2"’ÂÕ÷Ed%7FFRÓç46†ææVÄæÖRävWE7G&–ær‚’“°Ð¢–b‚WfVçDæÖRä—4V×G’‚’’°Ð¢F—FÆRäVæDf÷&ÖB…õB‚"ÒW2"’ÂWfVçDæÖRävWE7G&–ær‚’“°Ð¢ÐÐ¢ÒVÇ6R°Ð¢F—FÆR³ÒõB‚"ÂEd""“°Ð¢ÐÐ¢ÐÐ¢&WGW&âF—FÆS°Ð§ÐÐ Ð¤uT”B4Ö–äg&ÖS£¤vWEF–ÖTf÷&ÖB‚Ð§°Ð¢uT”B&WC°Ð¢–b‚Õ÷Õ2ÇÂ5T44TTDTB†Õ÷Õ2ÓävWEF–ÖTf÷&ÖB‚g&WB’’’°Ð¢54U%B„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTB“°Ð¢&WBÒD”ÔUôdõ$ÔEôäôäS°Ð¢ÐÐ¢&WGW&â&WC°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFTE…d7FGW2‚Ð§°Ð¢57G&–ærE…d–æfó°Ð¢òòvRöæÇ’7W÷'BvWGF–ær–æfòg&öÒÄbf–FVòFV6öFW"—2F†B—2v†Bv–ÆÂ&RW6VB“’RöbF†RF–ÖPÐ¢”&6Tf–ÇFW"¢$bÒf–æDf–ÇFW"„uT”EôÄef–FVòÂÕ÷t"“°Ð¢–b‡$b’°Ð¢–b„46öÕ•G#Ä”Äef–FVõ7FGW3âÄef–FVõ7FGW2Ò$b’°Ð¢6öç7BÅ5u5E"FV6öFW$æÖRÒÄef–FVõ7FGW2ÓävWD7F—fTFV6öFW$æÖR‚“°Ð¢–b†FV6öFW$æÖRÓÒçVÆÇG"ÇÂv766×†FV6öFW$æÖRÂÂ&f6öFV2"’ÓÒÇÂv766×†FV6öFW$æÖRÂÂ'v×c’ÖgB"’ÓÒÇÂv766×†FV6öFW$æÖRÂÂ&×6F²×f2"’ÓÒ’°Ð¢E…d–æfòÒõB‚$‚õrFV6öFW"¢æöæR"“°Ð¢ÒVÇ6R°Ð¢Õö%W6–ætE…dÒG'VS°Ð¢Õô…t66VÅG—RÒ4dtf–ÇFW$Äef–FVó£¤vWEW6W$g&–VæFÇ”FV6öFW$æÖR†FV6öFW$æÖR“°Ð¢E…d–æfòäf÷&ÖB…õB‚$‚õrFV6öFW"¢W2"’ÂÕô…t66VÅG—R“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b„E…d–æfòä—4V×G’‚’’°Ð¢E…d–æfòÒõB‚$‚õrFV6öFW"¢æöæRòVæ¶æ÷vâ"“°Ð¢ÐÐ¢vWE&VæFW&W'4FF‚’ÓæÕ÷7G$E…d–æfòÒE…d–æfó°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤vWDFV6öFW%G—R„57G&–ærbG—R’6öç7@Ð§°Ð¢–b‚ÕödVF–ôöæÇ’’°Ð¢–b†Õö%W6–ætE…d’°Ð¢G—RÒÕô…t66VÅG—S°Ð¢ÒVÇ6R°Ð¢G—RäÆöE7G&–ær„”E5õDôôÅD•õ4ôeEt$UôDT4ôD”är“°Ð¢ÐÐ¢&WGW&âG'VS°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤Ç•7V'F—FÆU&VæFW&–æu&ÖWFW'2„•7V%7G&VÒ¢7V%7G&VÒÂ&ööÂ%6V6öæF'’Ð§°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢–b†WFò%E2ÒG–æÖ–5ö67CÄ5&VæFW&VEFW‡E7V'F—FÆR£â‡7V%7G&VÒ’’°Ð¢&ööÂ$6†ævU7F÷&vU&W2ÒfÇ6S°Ð¢&ööÂ$6†ævU$6ö×ÒfÇ6S°Ð¢F÷V&ÆRE$6ö×Vç6F–öâÒã°Ð¢&ööÂ$¶VW7V7E&F–òÒ2æd¶VW7V7E&F–ó°Ð Ð¢56—¦R7¤7V7E&F–òÒÕ÷4ÓävWEf–FVõ6—¦R‡G'VR“°Ð¢56—¦R7¥f–FVôg&ÖS°Ð¢–b†Õ÷Õe$’’°Ð¢òòW6R”ÖEe$–æfòFòvWB6—¦Râ6VR‡GG¢òö'Vw2æÖG6†’ææWB÷f–Wrç‡ö–CÓƒ Ð¢Õ÷Õe$’ÓävWE6—¦R‚&÷&–v–æÅf–FVõ6—¦R"Âg7¥f–FVôg&ÖR“°Ð¢$¶VW7V7E&F–òÒG'VS°Ð¢ÒVÇ6R°Ð¢7¥f–FVôg&ÖRÒÕ÷4ÓävWEf–FVõ6—¦R†fÇ6R“°Ð¢ÐÐ Ð¢–b‡2æ%7V'F—FÆT$6ö×Vç6F–öâbb7¤7V7E&F–òæ7‚bb7¤7V7E&F–òæ7’bb7¥f–FVôg&ÖRæ7‚bb7¥f–FVôg&ÖRæ7’bb$¶VW7V7E&F–ò’°Ð¢–b‡%E2ÓæÕöÆ–÷WE&W2æ7‚â’°Ð¢E$6ö×Vç6F–öâÒ†F÷V&ÆR—7¤7V7E&F–òæ7‚¢%E2ÓæÕöÆ–÷WE&W2æ7’ò‡7¤7V7E&F–òæ7’¢%E2ÓæÕöÆ–÷WE&W2æ7‚“°Ð¢ÒVÇ6R°Ð¢E$6ö×Vç6F–öâÒ†F÷V&ÆR—7¤7V7E&F–òæ7‚¢7¥f–FVôg&ÖRæ7’ò‡7¤7V7E&F–òæ7’¢7¥f–FVôg&ÖRæ7‚“°Ð¢ÐÐ¢ÐÐ¢–b‡%E2ÓæÕöE$6ö×Vç6F–öâÒE$6ö×Vç6F–öâ’°Ð¢$6†ævU$6ö×ÒG'VS°Ð¢ÐÐ Ð¢–b‡%E2ÓæÕ÷7V'F—FÆUG—RÓÒ7V'F—FÆS£¤52ÇÂ%E2ÓæÕ÷7V'F—FÆUG—RÓÒ7V'F—FÆS£¥54’°Ð¢–b‡7¥f–FVôg&ÖRæ7‚â’°Ð¢–b‡%E2ÓæÕöÆ–÷WE&W2æ7‚ÓÒÇÂ%E2ÓæÕöÆ–÷WE&W2æ7’ÓÒ’°Ð¢$6†ævU7F÷&vU&W2Ò‡%E2ÓæÕ÷7F÷&vU&W2Ò7¥f–FVôg&ÖR“°Ð¢ÒVÇ6R°Ð¢$6†ævU7F÷&vU&W2Ò‡%E2ÓæÕ÷7F÷&vU&W2Ò%E2ÓæÕöÆ–÷WE&W2“°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢–b†$6†ævU7F÷&vU&W2’°Ð¢–b‡%E2ÓæÕöÆ–÷WE&W2æ7‚ÓÒÇÂ%E2ÓæÕöÆ–÷WE&W2æ7’ÓÒ’°Ð¢%E2ÓæÕ÷7F÷&vU&W2Ò7¥f–FVôg&ÖS°Ð¢ÒVÇ6R°Ð¢%E2ÓæÕ÷7F÷&vU&W2Ò%E2ÓæÕöÆ–÷WE&W3°Ð¢ÐÐ¢ÐÐ¢–b†$6†ævU$6ö×’°Ð¢%E2ÓæÕöU$6ö×Vç6F–öåG—RÒ56–×ÆUFW‡E7V'F—FÆS£¤U$6ö×Vç6F–öåG—S£¤U5D67W&FU6—¦Uô•5#°Ð¢%E2ÓæÕöE$6ö×Vç6F–öâÒE$6ö×Vç6F–öã°Ð¢ÐÐ Ð¢5E57G–ÆR7G–ÆRÒ2ç7V'F—FÆW4FVe7G–ÆS°Ð¢–b‡%E2ÓæÕö%W6–æuÆ–W$FVfVÇE7G–ÆR’°Ð¢%E2Óå6WDFVfVÇE7G–ÆR‡7G–ÆR“°Ð¢ÒVÇ6R–b‡%E2ÓävWDFVfVÇE7G–ÆR‡7G–ÆR’bb7G–ÆRç&VÆF—fUFòÓÒ5E57G–ÆS£¤UDòbb2ç7V'F—FÆW4FVe7G–ÆRç&VÆF—fUFòÒ5E57G–ÆS£¤UDò’°Ð¢7G–ÆRç&VÆF—fUFòÒ2ç7V'F—FÆW4FVe7G–ÆRç&VÆF—fUFó°Ð¢%E2Óå6WDFVfVÇE7G–ÆR‡7G–ÆR“°Ð¢ÐÐ¢%E2Óå6WD÷fW'&–FR‡2æ%7V'F—FÆT÷fW'&–FTFVfVÇE7G–ÆRÂ2æ%7V'F—FÆT÷fW'&–FTÆÅ7G–ÆW2Â2ç7V'F—FÆW4FVe7G–ÆR“°Ð¢–b†%6V6öæF'’’°Ð¢òòF†R6V6öæF'’7V'F—FÆRG&6²—2Çv—2æ6†÷&VBFòF†RF÷öbF†Rg&ÖPÐ¢%E2Óå6WDÆ–væÖVçB‡G'VRÂ2æä†÷%÷2Â2æå6V6öæF'•7V%fW%÷2ÂG'VR“°Ð¢ÒVÇ6R°Ð¢%E2Óå6WDÆ–væÖVçB‡2æd÷fW'&–FUÆ6VÖVçBÂ2æä†÷%÷2Â2æåfW%÷2“°Ð¢ÐÐ¢%E2Óå6WEW6Tg&VUG—R‡2æ%W6Tg&VUG—R“°Ð¢%E2Óå6WD÷VåG—TÆæt†–çB‡2ç7G$÷VåG—TÆæt†–çB“°Ð¢%E2ÓäFV–æ—B‚“°Ð¢ÐÐ¢&WGW&âG'VS°Ð¢ÒVÇ6R–b†WFòe52ÒG–æÖ–5ö67CÄ5fö%7V%6WGF–æw2£â‡7V%7G&VÒ’’°Ð¢°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢e52Óå6WDÆ–væÖVçB‡2æd÷fW'&–FUÆ6VÖVçBÂ2æä†÷%÷2Â2æåfW%÷2“°Ð¢ÐÐ¢&WGW&âG'VS°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¥WFFU7V'F—FÆU&VæFW&–æu&ÖWFW'2‚Ð§°Ð¢–b‚Õ÷4’°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢&ööÂ$–çfÆ–FFRÒÇ•7V'F—FÆU&VæFW&–æu&ÖWFW'2‚„•7V%7G&VÒ¢–Õ÷7W'&VçE7V$–çWBç7V%7G&VÒÂfÇ6R“°Ð¢–b†Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒ’°Ð¢$–çfÆ–FFRÃÒÇ•7V'F—FÆU&VæFW&–æu&ÖWFW'2‚„•7V%7G&VÒ¢–Õ÷6V6öæF'•7V$–çWBç7V%7G&VÒÂG'VR“°Ð¢ÐÐ¢–b†$–çfÆ–FFR’°Ð¢Õ÷4Óä–çfÆ–FFR‚“°Ð¢ÐÐ§ÐÐ Ð¥$TeD”ÔR4Ö–äg&ÖS£¤vWDfuF–ÖUW$g&ÖR‚’6öç7@Ð§°Ð¢$TeD”ÔR&VdfuF–ÖUW$g&ÖRÒã°Ð Ð¢–b„d”ÄTB†Õ÷%bÓævWEôfuF–ÖUW$g&ÖR‚g&VdfuF–ÖUW$g&ÖR’’’°Ð¢–b†Õ÷4’°Ð¢&VdfuF–ÖUW$g&ÖRÒãòÕ÷4ÓävWDe2‚“°Ð¢ÐÐ Ð¢&Vv–äVçVÔf–ÇFW'2†Õ÷t"ÂTbÂ$b’°Ð¢–b‡&VdfuF–ÖUW$g&ÖRâã’°Ð¢'&V³°Ð¢ÐÐ Ð¢&Vv–äVçVÕ–ç2‡$bÂUÂ–â’°Ð¢ÕôÔTD”õE•R×C°Ð¢–b…5T44TTDTB‡–âÓä6öææV7F–öäÖVF–G—R‚f×B’’’°Ð¢–b†×BæÖ¦÷'G—RÓÒÔTD”E•Uõf–FVòbb×Bæf÷&ÖGG—RÓÒdõ$ÔEõf–FVô–æfò’°Ð¢&VdfuF–ÖUW$g&ÖRÒ…$TeD”ÔR’‚…d”DTô”ädô„TDU"¢–×Bç$f÷&ÖB’ÓäfuF–ÖUW$g&ÖRò“cC°Ð¢'&V³°Ð¢ÒVÇ6R–b†×BæÖ¦÷'G—RÓÒÔTD”E•Uõf–FVòbb×Bæf÷&ÖGG—RÓÒdõ$ÔEõf–FVô–æfó"’°Ð¢&VdfuF–ÖUW$g&ÖRÒ…$TeD”ÔR’‚…d”DTô”ädô„TDU#"¢–×Bç$f÷&ÖB’ÓäfuF–ÖUW$g&ÖRò“cC°Ð¢'&V³°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢VæDVçVÕ–ç3°Ð¢ÐÐ¢VæDVçVÔf–ÇFW'3°Ð¢ÐÐ Ð¢òòF÷V&ÆRÖ6†V6²F†BF†RFWFV7F–öâ—26÷'&V7Bf÷"EdG0Ð¢EdEõf–FVôGG&–'WFW2dE#°Ð¢–b†Õ÷EdD’bb5T44TTDTB†Õ÷EdD’ÓävWD7W'&VçEf–FVôGG&–'WFW2‚edE"’’’°Ð¢F÷V&ÆR&F–ó°Ð¢–b…dE"çVÄg&ÖU&FRÓÒS’°Ð¢&F–òÒ#Rã¢&VdfuF–ÖUW$g&ÖS°Ð¢òò66WB#R÷"Sg0Ð¢–b‚—4æV&Ç”WVÂ‡&F–òÂãÂRÓ"’bb—4æV&Ç”WVÂ‡&F–òÂ"ãÂRÓ"’’°Ð¢&VdfuF–ÖUW$g&ÖRÒãò#Rã°Ð¢ÐÐ¢ÒVÇ6R°Ð¢&F–òÒ#’ã“r¢&VdfuF–ÖUW$g&ÖS°Ð¢òò66WB#’Ã“rÂS’ã“BÂ#2ã“sb÷"Crã“S"g0Ð¢–b‚—4æV&Ç”WVÂ‡&F–òÂãÂRÓ"’bb—4æV&Ç”WVÂ‡&F–òÂ"ãÂRÓ"Ð¢bb—4æV&Ç”WVÂ‡&F–òÂã#RÂRÓ"’bb—4æV&Ç”WVÂ‡&F–òÂ"ãRÂRÓ"’’°Ð¢&VdfuF–ÖUW$g&ÖRÒãò#’ã“s°Ð¢ÐÐ¢ÐÐ¢ÐÐ Ð¢&WGW&â&VdfuF–ÖUW$g&ÖS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öåf–FVõ6—¦T6†ævVB†6öç7B&ööÂ%v4VF–ôöæÇ’ò£ÒfÇ6R¢òÐ§°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBb`Ð¢‚‡2æe&VÖVÖ&W%¦ööÔÆWfVÂbb‡2ædÆ–Ö—Ev–æF÷u&÷÷'F–öç2ÇÂÕö$ÆÆ÷uv–æF÷u¦ööÒ’’ÇÂÕödVF–ôöæÇ’ÇÂ%v4VF–ôöæÇ’’b`Ð¢„—4gVÆÅ67&VVäÖöFR‚’ÇÂ—5¦ööÖVB‚’ÇÂ—4–6öæ–2‚’ÇÂ—4W&õ6æVB‚’’’°Ð¢56—¦Rf–FVõ6—¦S°Ð¢–b‚ÕödVF–ôöæÇ’bbÕö$ÆÆ÷uv–æF÷u¦ööÒ’°Ð¢f–FVõ6—¦RÒvWEf–FVõ6—¦R‚“°Ð¢ÐÐ¢–b‡f–FVõ6—¦Ræ7‚bbf–FVõ6—¦Ræ7’’°Ð¢¦ööÕf–FVõv–æF÷r†ÕöDÆ7Ef–FVõ66ÆTf7F÷"¢7FC£§7'B‚‡7FF–5ö67CÆF÷V&ÆSâ†ÕöÆ7Ef–FVõ6—¦Ræ7‚’¢ÕöÆ7Ef–FVõ6—¦Ræ7’Ð¢ò‡7FF–5ö67CÆF÷V&ÆSâ‡f–FVõ6—¦Ræ7‚’¢f–FVõ6—¦Ræ7’’’“°Ð¢ÒVÇ6R°Ð¢¦ööÕf–FVõv–æF÷r‚“°Ð¢ÐÐ¢ÐÐ¢Ö÷fUf–FVõv–æF÷r‚“°Ð§ÐÐ Ð§G—VFVb7G'V7B°Ð¢7V'F—FÆW4–æfò¢7V'F—FÆW4–æfó°Ð¢$ôôÂ$7F—fFS°Ð¢7FC£§7G&–ærf–ÆTæÖS°Ð¢7FC£§7G&–ærf–ÆT6öçFVçG3°Ð§Ò7V'F—FÆW4FF°Ð Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öäÆöE7V'F—FÆW2…u$Òu&ÒÂÅ$ÒÅ&ÒÐ§°Ð¢7V'F—FÆW4FFbFFÒ¢…7V'F—FÆW4FF¢–Å&Ó°Ð Ð¢4WFõG#Ä5&VæFW&VEFW‡E7V'F—FÆSâ%E2„DT%TuôäUr5&VæFW&VEFW‡E7V'F—FÆR‚fÕö757V$Æö6²’“°Ð¢–b‡%E2’°Ð¢–b‡%E2Óä÷Vâ„57G&–ær†FFç7V'F—FÆW4–æfòÓå&÷f–FW"‚’ÓäF—7Æ”æÖR‚’æ5÷7G"‚’’ÀÐ¢„%•DR¢’„Å55E"–FFæf–ÆT6öçFVçG2æ5÷7G"‚’Â†–çB–FFæf–ÆT6öçFVçG2æÆVæwF‚‚’ÂDTdTÅEô4„%4UBÀÐ¢UDc…Fób†FFæf–ÆTæÖRæ5÷7G"‚’’Â7V'F—FÆS£¤†V&–æt–×—&VEG—R†FFç7V'F—FÆW4–æfòÓæ†V&–æt–×—&VB’ÀÐ¢•4ôÆæs£¤•4óc3“FôÆ6–B†FFç7V'F—FÆW4–æfòÓæÆæwVvT6öFRæ5÷7G"‚’’’bb%E2ÓävWE7G&VÔ6÷VçB‚’â’°Ð¢Õ÷væE7V'F—FÆW4F÷væÆöDF–ÆöräFôF÷væÆöFVB‚¦FFç7V'F—FÆW4–æfò“°Ð¢6–bU4UôÄ”$50Ð¢–b‡%E2ÓæÕôÆ–&746öçFW‡Bä—4Æ–&747F—fR‚’’°Ð¢%E2ÓæÕôÆ–&746öçFW‡Bå6WDf–ÇFW$w&‚†Õ÷t"“°Ð¢ÐÐ¢6VæF–`Ð¢7V'F—FÆT–çWB7V$VÆVÖVçBÒ%E2äFWF6‚‚“°Ð¢Õ÷7V%7G&V×2äFEF–Â‡7V$VÆVÖVçB“°Ð¢–b†FFæ$7F—fFR’°Ð¢ÕôW‡FW&æÅ7V'7G&V×2çW6…ö&6²‡7V$VÆVÖVçBç7V%7G&VÒ“°Ð¢6WE7V'F—FÆR‡7V$VÆVÖVçBç7V%7G&VÒ“°Ð Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b‡2æd¶VW†—7F÷'’bb2æ%&VÖVÖ&W%G&6µ6VÆV7F–öâbb2æ$WFõ6fTF÷væÆöFVE7V'F—FÆW2’°Ð¢2äÕ%RåWFFT7W'&VçE7V'F—FÆUG&6²„vWE6VÆV7FVE7V'F—FÆUG&6´–æFW‚‚’“°Ð¢ÐÐ¢ÐÐ¢&WGW&âE%TS°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&âdÅ4S°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öävWE7V'F—FÆW2…u$ÒÂÅ$ÒÅ&ÒÐ§°Ð¢6†V6µö–çFW"†Å&ÒÂdÅ4R“°Ð Ð¢–çBâÒ°Ð¢7V'F—FÆT–çWB¢7V$–çWBÒvWE7V'F—FÆT–çWB†âÂG'VR“°Ð¢6†V6µö–çFW"‡7V$–çWBÂdÅ4R“°Ð Ð¢4Å4”B6Ç6–C°Ð¢–b„d”ÄTB‡7V$–çWBÓç7V%7G&VÒÓävWD6Æ74”B‚f6Ç6–B’’ÇÂ6Ç6–BÒõ÷WV–Föb„5&VæFW&VEFW‡E7V'F—FÆR’’°Ð¢&WGW&âdÅ4S°Ð¢ÐÐ Ð¢5&VæFW&VEFW‡E7V'F—FÆR¢%E2Ò„5&VæFW&VEFW‡E7V'F—FÆR¢’„•7V%7G&VÒ¢—7V$–çWBÓç7V%7G&VÓ°Ð¢òòöæÇ’f÷"W‡FW&æÂFW‡B7V'F—FÆW0Ð¢–b‡%E2ÓæÕ÷F‚ä—4V×G’‚’’°Ð¢&WGW&âdÅ4S°Ð¢ÐÐ Ð¢7V'F—FÆW4–æfò¢7V'F—FÆW4–æfòÒ&V–çFW'&WEö67CÅ7V'F—FÆW4–æfò£â†Å&Ò“°Ð Ð¢7V'F—FÆW4–æfòÓävWDf–ÆT–æfò‚“°Ð¢7V'F—FÆW4–æfòÓç&VÆV6TæÖW2æV×Æ6Uö&6²…UDceFó‚‡%E2ÓæÕöæÖR’“°Ð¢–b‡7V'F—FÆW4–æfòÓæ†V&–æt–×—&VBÓÒ7V'F—FÆS£¤„•õTä´äõtâ’°Ð¢7V'F—FÆW4–æfòÓæ†V&–æt–×—&VBÒ%E2ÓæÕöT†V&–æt–×—&VC°Ð¢ÐÐ Ð¢–b‚7V'F—FÆW4–æfòÓæÆæwVvT6öFRæÆVæwF‚‚’bb%E2ÓæÕöÆ6–Bbb%E2ÓæÕöÆ6–BÒÄ4”B‚Ó’’°Ð¢57G&–ær7G#°Ð¢vWDÆö6ÆU7G&–ær‡%E2ÓæÕöÆ6–BÂÄô4ÄUõ4•4óc3”ÄätäÔRÂ7G"“°Ð¢7V'F—FÆW4–æfòÓæÆæwVvT6öFRÒUDceFó‚‡7G"“°Ð¢ÐÐ Ð¢7V'F—FÆW4–æfòÓæg&ÖU&FRÒÕ÷4ÓävWDe2‚“°Ð¢–çBFVÆ’ÒÕ÷4ÓävWE7V'F—FÆTFVÆ’‚“°Ð¢–b‡%E2ÓæÕöÖöFRÓÒe$ÔR’°Ð¢FVÆ’Ò7FC£¦Ç&÷VæB†FVÆ’¢7V'F—FÆW4–æfòÓæg&ÖU&FRòã“°Ð¢ÐÐ Ð¢6öç7B57G&–æurf×B„Â"VEÆâS&C¢S&C¢S&BÂS6BÒÓâS&C¢S&C¢S&BÂS6EÆâW5ÆåÆâ"“°Ð¢57G&–æur6öçFVçC°Ð¢4WFôÆö6²4WFôÆö6²‚fÕö757V$Æö6²“°Ð¢f÷"†–çB’ÒÂ¢Ò–çB‡%E2ÓävWD6÷VçB‚’’Â²Ò²’Â£²’²²’°Ð¢–çBCÒ†–çB’…%C$Õ2‡%E2ÓåG&ç6ÆFU7F'B†’Â7V'F—FÆW4–æfòÓæg&ÖU&FR’’²FVÆ’“°Ð¢–b‡CÂ’°Ð¢²²³°Ð¢6öçF–çVS°Ð¢ÐÐ Ð¢–çBC"Ò†–çB’…%C$Õ2‡%E2ÓåG&ç6ÆFTVæB†’Â7V'F—FÆW4–æfòÓæg&ÖU&FR’’²FVÆ’“°Ð Ð¢–çB†ƒÒ‡Còcòcò“°Ð¢–çBÖÓÒ‡Còcò’Rc°Ð¢–çB73Ò‡Cò’Rc°Ð¢–çB×3Ò‡C’R°Ð¢–çB†ƒ"Ò‡C"òcòcò“°Ð¢–çBÖÓ"Ò‡C"òcò’Rc°Ð¢–çB73"Ò‡C"ò’Rc°Ð¢–çB×3"Ò‡C"’R°Ð Ð¢6öçFVçBäVæDf÷&ÖB†f×BÂ’Ò²²Â†ƒÂÖÓÂ73Â×3Â†ƒ"ÂÖÓ"Â73"Â×3"Â%E2ÓävWE7G%r†’ÂfÇ6R’ävWE7G&–ær‚’“°Ð¢ÐÐ Ð¢7V'F—FÆW4–æfòÓæf–ÆT6öçFVçG2ÒUDceFó‚†6öçFVçB“°Ð¢&WGW&âE%TS°Ð§ÐÐ Ð§7FF–26öç7B57G&–ær–FÅ÷v†—FVÆ—7EµÒÒ°Ð¢õB‚'–÷WGV&Ræ6öÒò"’ÀÐ¢õB‚'–÷WGRæ&Rò"’ÀÐ¢õB‚'Gv—F6‚çGbò"’ÀÐ¢õB‚'Gv—F6‚æ6öÒò"’ÀÐ¢õB‚&–ç7Fw&Òæ6öÒò"’ÀÐ¢õB‚&f6V&öö²æ6öÒò"’ÀÐ¢õB‚'F–·Fö²æ6öÒò"’ÀÐ¢õB‚'f–ÖVòæ6öÒò"’ÀÐ¢õB‚&F–Ç–Ö÷F–öâæ6öÒò"’ÀÐ¢õB‚&7'Væ6‡—&öÆÂæ6öÒò"’ÀÐ¢õB‚&&&2æ6òçV²ò"’ÀÐ¢õB‚'÷&æ‡V"æ6öÒò"’ÀÐ¢õB‚'‡f–FV÷2æ6öÒò"’ÀÐ¢õB‚'††×7FW"æ6öÒò"’ÀÐ¢õB‚'–÷W÷&âæ6öÒò"’ÀÐ¢õB‚'FæfÆ—‚æ6öÒò"’ÀÐ§Ó°Ð Ð§7FF–26öç7B57G&–ær–FÅö&Æ6¶Æ—7EµÒÒ°Ð¢õB‚&vöövÆWf–FVòæ6öÒ÷f–FV÷Æ–&6²"’ÂòòÇ&VG’&ö6W76VBU$ÀÐ¢õB‚&vöövÆWf–FVòæ6öÒö’öÖæ–fW7B"’ÀÐ¢õB‚$#rããã¢"’ÂòòÆö6ÂU$ÀÐ¢õB‚'6VæÆ‡F’æf’ò"Ð§Ó°Ð Ð¦&ööÂ4Ö–äg&ÖS£¤—4öå”DÅv†—FVÆ—7B„57G&–ærW&Â’°Ð¢f÷"†–çB’Ò²’Âö6÷VçFöb‡–FÅ÷v†—FVÆ—7B“²’²²’°Ð¢–b‡W&Âäf–æB‡–FÅ÷v†—FVÆ—7E¶•Ò’ãÒ’°Ð¢&WGW&âG'VS°Ð¢ÐÐ¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤6å6VæEFõ–÷WGV&TDÂ†6öç7B57G&–ærW&ÂÐ§°Ð¢–b‡W&ÂäÆVgBƒB’äÖ¶TÆ÷vW"‚’ÓÒõB‚&‡GG"’’°Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð¢–b‚2æ%W6U”DÂ’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢òò&Æ6¶Æ—7C¢FöâwBW6Rf÷"•FG&W76W0Ð¢7FC£§v6ÖF6‚&VvÖF6ƒ°Ð¢7FC£§w&VvW‚&VvW‡„Å""†‡GG3ó¥ÂõÂò…ÆG³Ã7ÕÂâ—³7ÕÆG³Ã7Òâ¢’"“°Ð¢–b‡7FC£§&VvW…öÖF6‚‡W&ÂävWE7G&–ær‚’Â&VvÖF6‚Â&VvW‡’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢òòv†—FVÆ—7C¢÷VÆ"7W÷'FVB6—FW0Ð¢–b„—4öå”DÅv†—FVÆ—7B‡W&Â’’°Ð¢&WGW&âG'VS°Ð¢ÐÐ Ð¢òò&Æ6¶Æ—7C¢Vç7W÷'FVB6—FW2v†W&R”DÂ6W6W2âW'&÷"÷"ÆöærFVÆÐ¢f÷"†–çB’Ò²’Âö6÷VçFöb‡–FÅö&Æ6¶Æ—7B“²’²²’°Ð¢–b‡W&Âäf–æB‡–FÅö&Æ6¶Æ—7E¶•ÒÂr’â’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ Ð¢òò&Æ6¶Æ—7C¢U$Âö–çG2Fòf–ÆPÐ¢57G&–ær&6WW&Ã°Ð¢–çBÒW&Âäf–æB…õB‚sòr’“°Ð¢–b‡â’°Ð¢&6WW&ÂÒW&ÂäÆVgB‡“°Ð¢ÒVÇ6R°Ð¢&6WW&ÂÒW&Ã°Ð¢ÒW&ÂävWDÆVæwF‚‚“°Ð¢ÐÐ¢–çBÒ&6WW&Âå&WfW'6Tf–æB…õB‚râr’“°Ð¢–b‡âbb‡ÒÃÒb’’°Ð¢57G&–ærW‡BÒ&6WW&ÂäÖ–B‡“°Ð¢–b†W‡BÓÒÂ"æÓ7S‚"ÇÂW‡BÓÒÂ"æ×B"’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢–b‡2æÕôf÷&ÖG2äf–æDW‡B†W‡B’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢ÐÐ Ð¢&WGW&âG'VS°Ð¢ÐÐ¢&WGW&âfÇ6S°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¥&ö6W75–÷WGV&TDÅU$Â„57G&–ærW&ÂÂ&ööÂVæBÂ&ööÂ&WÆ6RÐ§°Ð¢WFòb2Òg„vWD6WGF–æw2‚“°Ð¢4FÄÆ—7CÄ5–÷WGV&TDÄ–ç7Fæ6S£¥”DÅ7G&VÕU$Ãâ7G&V×3°Ð¢4FÄÆ—7CÄ57G&–æsâf–ÆVæÖW3°Ð¢5–÷WGV&TDÄ–ç7Fæ6R–FÃ°Ð¢5–÷WGV&TDÄ–ç7Fæ6S£¥”DÅÆ–Æ—7D–æfòÆ—7F–æfó°Ð¢57G&–ærW6W&vVçC°Ð Ð¢Õ÷7–FÄÆ7E&ö6W75U$ÂÒW&Ã°Ð Ð¢Õ÷væE7FGW4&"å6WE7FGW4ÖW76vR…&W57G"„”E5ô4ôåE$ôÅ5õ”õUET$TDÂ’“°Ð Ð¢–b‚–FÂå'Vâ‡W&Â’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ¢–b‚–FÂävWD‡GG7G&V×2‡7G&V×2ÂÆ—7F–æfòÂW6W&vVçB’’°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢–b‚VæBbb&WÆ6R’°Ð¢Õ÷væEÆ–Æ—7D&"äV×G’‚“°Ð¢ÐÐ Ð¢57G&–ære÷F—FÆS°Ð Ð¢f÷"‡Vç6–væVB–çB’Ò²’Â7G&V×2ävWD6÷VçB‚“²’²²’°Ð¢WFò7G&VÒÒ7G&V×2ävWDB‡7G&V×2äf–æD–æFW‚†’’“°Ð¢57G&–ære÷W&ÂÒ7G&VÒçf–FVõ÷W&Ã°Ð¢57G&–ær÷W&ÂÒ7G&VÒæVF–õ÷W&Ã°Ð¢f–ÆVæÖW2å&VÖ÷fTÆÂ‚“°Ð¢–b‚e÷W&Âä—4V×G’‚’bb‚2æ%”DÄVF–ôöæÇ’ÇÂ÷W&Âä—4V×G’‚’’’°Ð¢f–ÆVæÖW2äFEF–Â‡e÷W&Â“°Ð Ð¢ÐÐ¢–b‚÷W&Âä—4V×G’‚’’°Ð¢f–ÆVæÖW2äFEF–Â†÷W&Â“°Ð¢ÐÐ¢57G&–ærF—FÆRÒ7G&VÒçF—FÆS°Ð¢57G&–ær6V6öæ–C°Ð¢–b‡7G&VÒç6V6öåöçVÖ&W"ÒÓ’°Ð¢6V6öæ–Bäf÷&ÖB…õB‚%2S&B"’Â7G&VÒç6V6öåöçVÖ&W"“°Ð¢ÐÐ¢57G&–ærW—6öFV–C°Ð¢–b‡7G&VÒæW—6öFUöçVÖ&W"ÒÓ’°Ð¢W—6öFV–Bäf÷&ÖB…õB‚$RS&B"’Â7G&VÒæW—6öFUöçVÖ&W"“°Ð¢ÐÐ¢57G&–ærW––C°Ð¢–b‚6V6öæ–Bä—4V×G’‚’ÇÂW—6öFV–Bä—4V×G’‚’’°Ð¢W––Bäf÷&ÖB…õB‚"W2W2â"’Â7FF–5ö67CÄÅ5u5E#â‡6V6öæ–B’Â7FF–5ö67CÄÅ5u5E#â†W—6öFV–B’“°Ð¢ÐÐ¢57G&–ær6V6öã°Ð¢–b‚7G&VÒç6W&–W2ä—4V×G’‚’’°Ð¢6V6öâÒ7G&VÒç6W&–W3°Ð¢57G&–ærB‡7G&VÒç6V6öâäÆVgBƒb’“°Ð¢–b‚7G&VÒç6V6öâä—4V×G’‚’bb‡BäÖ¶TÆ÷vW"‚’ÒõB‚'6V6öâ"’ÇÂ7G&VÒç6V6öåöçVÖ&W"ÓÒÓ’’°Ð¢6V6öâ³ÒõB‚""’²7G&VÒç6V6öã°Ð¢ÐÐ¢6V6öâ³ÒõB‚"Ò"“°Ð¢ÐÐ¢VÇ6R–b‚7G&VÒç6V6öâä—4V×G’‚’’°Ð¢57G&–ærB‡7G&VÒç6V6öâäÆVgBƒb’“°Ð¢–b‡BäÖ¶TÆ÷vW"‚’ÒõB‚'6V6öâ"’ÇÂ7G&VÒç6V6öåöçVÖ&W"ÓÒÓ’°Ð¢6V6öâÒ7G&VÒç6V6öâ²õB‚"Ò"“°Ð¢ÐÐ¢ÐÐ¢F—FÆRäf÷&ÖB…õB‚"W2W2W2"’Â7FF–5ö67CÄÅ5u5E#â†W––B’Â7FF–5ö67CÄÅ5u5E#â‡6V6öâ’Â7FF–5ö67CÄÅ5u5E#â‡F—FÆR’“°Ð¢–b†’ÓÒ’e÷F—FÆRÒF—FÆS°Ð Ð¢57G&–ær–FÅ÷7&2Ò7G&VÒçvV'vU÷W&Âä—4V×G’‚’òW&Â¢7G&VÒçvV'vU÷W&Ã°Ð¢–b†’ÓÒ’Õ÷7–FÄÆ7E&ö6W75U$ÂÒ–FÅ÷7&3°Ð Ð¢–çBF&vWFÆVâÒF—FÆRävWDÆVæwF‚‚’âòS¢SÒF—FÆRävWDÆVæwF‚‚“°Ð¢57G&–ær6†÷'E÷W&ÂÒ6†÷'FVåU$Â‡–FÅ÷7&2ÂF&vWFÆVâÂG'VR“°Ð¢ Ð¢–b‡–FÅ÷7&2ÓÒf–ÆVæÖW2ävWD†VB‚’’°Ð¢òò&ö6W76VBU$Â—26ÖR2–çWBÂ6â†Vâf÷"D4‚Öæ–fW7Bf–ÆW2â6ÆV"6÷W&6RU$ÂFòfö–B&W&ö6W76–æràÐ¢–FÅ÷7&2ÒõB‚""“°Ð¢ÐÐ Ð¢–b‡&WÆ6R’°Ð¢Õ÷væEÆ–Æ—7D&"å&WÆ6T7W'&VçD—FVÒ†f–ÆVæÖW2ÂçVÆÇG"ÂF—FÆR²"‚"²6†÷'E÷W&Â²"’"Â–FÅ÷7&2ÂW6W&vVçBÂõB‚""’Âg7G&VÒç7V'F—FÆW2“°Ð¢'&V³°Ð¢ÒVÇ6R°Ð¢Õ÷væEÆ–Æ—7D&"äVæB†f–ÆVæÖW2ÂfÇ6RÂçVÆÇG"ÂF—FÆR²"‚"²6†÷'E÷W&Â²"’"Â–FÅ÷7&2ÂW6W&vVçBÂõB‚""’Âg7G&VÒç7V'F—FÆW2“°Ð¢ÐÐ¢ÐÐ Ð¢–b‡2æd¶VW†—7F÷'’’°Ð¢WFò¢×'RÒg2äÕ%S°Ð¢&V6VçDf–ÆTVçG'’#°Ð¢×'RÓäÆöDÖVF–†—7F÷'”VçG'”dâ†Õ÷7–FÄÆ7E&ö6W75U$ÂÂ"“°Ð¢–b‡7G&V×2ävWD6÷VçB‚’â’°Ð¢WFò‚Ò7G&V×2ävWD†VB‚“°Ð¢–b‚‚ç6W&–W2ä—4V×G’‚’’°Ð¢"çF—FÆRÒ‚ç6W&–W3°Ð¢–b‚‚ç6V6öâä—4V×G’‚’’°Ð¢"çF—FÆR³ÒõB‚"Ò"’²‚ç6V6öã°Ð¢ÐÐ¢ÐÐ¢VÇ6R–b‚‚ç6V6öâä—4V×G’‚’’°Ð¢"çF—FÆRÒ‚ç6V6öã°Ð¢ÐÐ¢VÇ6R–b‚Æ—7F–æfòçF—FÆRä—4V×G’‚’’°Ð¢–b‚Æ—7F–æfòçWÆöFW"ä—4V×G’‚’’"çF—FÆRäf÷&ÖB…õB‚"W2ÒW2"’Â7FF–5ö67CÄÅ5u5E#â†Æ—7F–æfòçWÆöFW"’Â7FF–5ö67CÄÅ5u5E#â†Æ—7F–æfòçF—FÆR’“°Ð¢VÇ6R"çF—FÆRÒÆ—7F–æfòçF—FÆS°Ð¢ÐÐ¢VÇ6R"çF—FÆRÒe÷F—FÆS°Ð¢ÐÐ¢VÇ6R–b‡7G&V×2ävWD6÷VçB‚’ÓÒ’°Ð¢"çF—FÆRÒe÷F—FÆS°Ð¢ÐÐ¢×'RÓäFB‡"ÂfÇ6R“°Ð¢ÐÐ Ð¢–b‚VæBbb‚&WÆ6RÇÂÕ÷væEÆ–Æ—7D&"ävWD6÷VçB‚’ÓÒ’’°Ð¢Õ÷væEÆ–Æ—7D&"å6WDf—'7B‚“°Ð¢ÐÐ¢&WGW&âG'VS°Ð§ÐÐ Ð¦&ööÂ4Ö–äg&ÖS£¤F÷væÆöEv—F…–÷WGV&TDÂ„57G&–ærW&ÂÂ57G&–ærf–ÆVæÖRÐ§°Ð¢$ô4U55ô”ädõ$ÔD”ôâ&ö5ö–æfó°Ð¢5D%EU”ädò7F'GWö–æfó°Ð¢6öç7BWFòb2Òg„vWD6WGF–æw2‚“°Ð Ð¢&ööÂ—FFÇÒG'VS°Ð¢57G&–ær&w2ÒõB‚%Â""’²vWE”DÄW†UF‚‚g—FFÇ’²õB‚%Â"ÒÖ6öç6öÆR×F—FÆRÂ""’²W&Â²õB‚%Â""“°Ð¢–b‚2ç5”DÄ6öÖÖæDÆ–æRä—4V×G’‚’’°Ð¢&w2äVæB…õB‚""’“°Ð¢&w2äVæB‡2ç5”DÄ6öÖÖæDÆ–æR“°Ð¢ÐÐ¢–b‡2æ%”DÄVF–ôöæÇ’bb‡2ç5”DÄ6öÖÖæDÆ–æRäf–æB…õB‚"Öb"’’Â’’°Ð¢&w2äVæB…õB‚"Öb&W7FVF–ò"’“°Ð¢ÐÐ¢–b‡2ç5”DÄ6öÖÖæDÆ–æRäf–æB…õB‚"Öò"’’Â’°Ð¢&w2äVæB…õB‚"ÖòÂ""²f–ÆVæÖR²%Â""’“°Ð¢ÐÐ Ð¢¦W&ôÖVÖ÷'’‚g&ö5ö–æfòÂ6—¦Vöb…$ô4U55ô”ädõ$ÔD”ôâ’“°Ð¢¦W&ôÖVÖ÷'’‚g7F'GWö–æfòÂ6—¦Vöb…5D%EU”ädò’“°Ð¢7F'GWö–æfòæ6"Ò6—¦Vöb…5D%EU”ädò“°Ð Ð¢–b‚7&VFU&ö6W72„åTÄÂÂ&w2ävWD'VffW"‚’ÂåTÄÂÂåTÄÂÂfÇ6RÂÀÐ¢åTÄÂÂåTÄÂÂg7F'GWö–æfòÂg&ö5ö–æfò’’°Ð¢g„ÖW76vT&÷‚…õB‚$âW'&÷"ö67W'&VBv†–ÆRGFV×F–ærFò'Vâ—BÖFÇ÷–÷WGV&RÖFÂ"’ÂÔ%ô”4ôäU%$õ"Â“°Ð¢&WGW&âfÇ6S°Ð¢ÐÐ Ð¢6Æ÷6T†æFÆR‡&ö5ö–æfòæ…&ö6W72“°Ð¢6Æ÷6T†æFÆR‡&ö5ö–æfòæ…F‡&VB“°Ð Ð¢&WGW&âG'VS°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öå6WGF–æt6†ævR…T”åBTfÆw2ÂÅ5E5E"Ç7¥6V7F–öâÐ§°Ð¢õ÷7WW#£¤öå6WGF–æt6†ævR‡TfÆw2ÂÇ7¥6V7F–öâ“°Ð¢–b…5•õ4UDäôä4Ä”TåDÔUE$”52ÓÒTfÆw2’°Ð¢4Õ5F†VÖUWF–Ã£¤vWDÖWG&–72‡G'VR“°Ð¢4Õ5F†VÖTÖVçS£¦6ÆV$F–ÖVç6–öç2‚“°Ð¢–b†çVÆÇG"ÒFVfVÇDÕ5F†VÖTÖVçR’°Ð¢WFFUT”ÆæwVvR‚“²òö6†Vv’Fò&V'V–ÆBÖVçW2Ò×vRvçBFòFòF†—2Fòf÷&6RF†VÒFò&RÖÖV7W&PÐ¢ÐÐ¢&V6Æ4Æ–÷WB‚“°Ð¢ÐÐ§ÐÐ Ð¤$ôôÂ4Ö–äg&ÖS£¤öäÖ÷W6Uv†VVÂ…T”åBäfÆw2Â6†÷'B¤FVÇFÂ5ö–çBö–çB’°Ð¢–b†Õö%W6U6VVµ&Wf–WrbbÕ÷væE&Uf–Wrä—5v–æF÷uf—6–&ÆR‚’’°Ð Ð¢–çB6VV²ÐÐ¢äfÆw2ÓÒÔµõ4„”eBò Ð¢äfÆw2ÓÒÔµô4ôåE$ôÂò¢S°Ð Ð¢¤FVÇFâò6WD7W'6÷%÷2‡ö–çBç‚²6VV²Âö–çBç’’ Ð¢¤FVÇFÂò6WD7W'6÷%÷2‡ö–çBç‚Ò6VV²Âö–çBç’’¢6WD7W'6÷%÷2‡ö–çBç‚Âö–çBç’“°Ð Ð¢&WGW&â°Ð¢ÐÐ¢&WGW&âõ÷7WW#£¤öäÖ÷W6Uv†VVÂ†äfÆw2Â¤FVÇFÂö–çB“°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤öäÖ÷W6T…v†VVÂ…T”åBäfÆw2Â6†÷'B¤FVÇFÂ5ö–çBB’°Ð¢–b†Õ÷væEf–WrbbÕ÷væEf–WräöäÖ÷W6T…v†VVÄ–×Â†äfÆw2Â¤FVÇFÂB’’°Ð¢òô…t„TTÂ—26VçBFò7F—fRv–æF÷rÂ6òvR†fRFòÖçVÆÇ’72—BFò4Ö÷W6UvæBFòG&†÷F¶W—0Ð¢&WGW&ã°Ð¢ÐÐ¢õ÷7WW#£¤öäÖ÷W6T…v†VVÂ†äfÆw2Â¤FVÇFÂB“°Ð§ÐÐ Ð¤4†F×d6Æ—–æfó£¤$DÕdÖWF4Ö–äg&ÖS£¤vWD$DÕdÖWF‚Ð§°Ð¢&WGW&âÕô$DÖWFävWD†VB‚“°Ð§ÐÐ Ð¤$ôôÂ4Ö–äg&ÖS£¤VæDÖVçTW‚„4ÖVçRbÖVçRÂT”åBäfÆw2ÂT”åBä”DæWt—FVÒÂ57G&–ærbFW‡BÐ§°Ð¢FW‡BÒ6æ—F—¦TÖVçTÆ&VÂ‡FW‡B“°Ð¢WFò%&W7VÇBÒÖVçRäVæDÖVçR†äfÆw2Âä”DæWt—FVÒÂFW‡BävWE7G&–ær‚’“°Ð¢–b†%&W7VÇBbb†äfÆw2bÔeôDTdTÅB’’°Ð¢%&W7VÇBÒÖVçRå6WDFVfVÇD—FVÒ†ä”DæWt—FVÒ“°Ð¢ÐÐ¢&WGW&â%&W7VÇC°Ð§ÐÐ Ð¤57G&–ær4Ö–äg&ÖS£¦vWD&W7EF—FÆR†&ööÂeF—FÆT&%FW‡EF—FÆR’°Ð¢57G&–ærF—FÆS°Ð¢–b†eF—FÆT&%FW‡EF—FÆRbbÕ÷ÔÔ5³Ò’°Ð¢f÷"†6öç7BWFòbÔÔ2¢Õ÷ÔÔ2’°Ð¢–b‡ÔÔ2’°Ð¢46öÔ%5E"'7G#°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEõF—FÆR‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢F—FÆRÒ'7G"æÕ÷7G#°Ð¢F—FÆRåG&–Ò‚“°Ð¢–b‚F—FÆRä—4V×G’‚’’°Ð¢&WGW&âF—FÆS°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’ÂG'VR’bbÆ’æÕöÆ&VÂbbÆ’æÕöÆ&VÂä—4V×G’‚’’°Ð¢–b†eF—FÆT&%FW‡EF—FÆRÇÂÆ’æÕö%–÷WGV&TDÂ’°Ð¢F—FÆRÒÆ’æÕöÆ&VÃ°Ð¢&WGW&âF—FÆS°Ð¢ÐÐ¢ÐÐ Ð¢57G&–æurW‡BÒvWDf–ÆTW‡B„vWDf–ÆTæÖR‚’“°Ð¢–b†W‡BÓÒ"æ×Ç2"bbÕö$†4$DÖWF’°Ð¢F—FÆRÒvWD$DÕdÖWF‚’çF—FÆS°Ð¢&WGW&âF—FÆS°Ð¢ÒVÇ6R–b†W‡BÒ"æ×Ç2"’°Ð¢Õö$†4$DÖWFÒfÇ6S°Ð¢Õô$DÖWFå&VÖ÷fTÆÂ‚“°Ð¢ÐÐ Ð¢&WGW&âÂ"#°Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅ6WDÖVF–‚’°Ð¢–b†ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"bbÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2’°Ð¢E$4R…õB‚$4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅ6WDÖVF–‚•Æâ"’“°Ð¢…$U5TÅB&WBÒ5ôô³°Ð¢&ööÂ†fU÷6V6öæF'•÷F—FÆRÒfÇ6S°Ð Ð¢57G&–ærF—FÆRÒvWD&W7EF—FÆR‚“°Ð¢–b‡F—FÆRä—4V×G’‚’’°Ð¢F—FÆRÒvWDf–ÆTæÖR‚“°Ð¢ÐÐ Ð¢57G&–ærWF†÷#°Ð¢–b†Õ÷ÔÔ5³Ò’°Ð¢f÷"†6öç7BWFòbÔÔ2¢Õ÷ÔÔ2’°Ð¢–b‡ÔÔ2’°Ð¢46öÔ%5E"'7G#°Ð¢–b…5T44TTDTB‡ÔÔ2ÓævWEôWF†÷$æÖR‚f'7G"’’bb'7G"äÆVæwF‚‚’’°Ð¢WF†÷"Ò'7G"æÕ÷7G#°Ð¢WF†÷"åG&–Ò‚“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢òò6WBÖVF–FWF–Ç0Ð¢–b†ÕödVF–ôöæÇ’’°Ð¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓçWEõG—R„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µG—Uô×W6–2“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢WEõG—RW'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢46öÕG#Ä$“£¥v–æF÷w3£¤ÖVF–£¤”×W6–4F—7Æ•&÷W'F–W3â×W6–4F—7Æ•&÷W'F–W3°Ð¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓævWEô×W6–5&÷W'F–W2‚g×W6–4F—7Æ•&÷W'F–W2“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢vWEô×W6–5&÷W'F–W2W'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b‚F—FÆRä—4V×G’‚’’°Ð¢…5E$”ärGF—FÆS°Ð¢–b…v–æF÷w47&VFU7G&–ær‡F—FÆRävWE7G&–ær‚’ÂF—FÆRävWDÆVæwF‚‚’ÂgGF—FÆR’ÓÒ5ôô²’°Ð¢&WBÒ×W6–4F—7Æ•&÷W'F–W2ÓçWEõF—FÆR‡GF—FÆR“°Ð¢54U%B‡&WBÓÒ5ôô²“°Ð¢ÐÐ¢ÐÐ¢–b‚WF†÷"ä—4V×G’‚’’°Ð¢…5E$”ärFV×°Ð¢–b…v–æF÷w47&VFU7G&–ær†WF†÷"ävWE7G&–ær‚’ÂWF†÷"ävWDÆVæwF‚‚’ÂgFV×’ÓÒ5ôô²’°Ð¢&WBÒ×W6–4F—7Æ•&÷W'F–W2ÓçWEô'F—7B‡FV×“°Ð¢54U%B‡&WBÓÒ5ôô²“°Ð¢ÐÐ¢ÐÐ¢ÒVÇ6R°Ð¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓçWEõG—R„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µG—Uõf–FVò“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢WEõG—RW'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢46öÕG#Ä$“£¥v–æF÷w3£¤ÖVF–£¤•f–FVôF—7Æ•&÷W'F–W3âf–FVôF—7Æ•&÷W'F–W3°Ð¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓævWEõf–FVõ&÷W'F–W2‚gf–FVôF—7Æ•&÷W'F–W2“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢vWEõf–FVõ&÷W'F–W2W'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢–b‚F—FÆRä—4V×G’‚’’°Ð¢…5E$”ärGF—FÆS°Ð¢–b…v–æF÷w47&VFU7G&–ær‡F—FÆRävWE7G&–ær‚’ÂF—FÆRävWDÆVæwF‚‚’ÂgGF—FÆR’ÓÒ5ôô²’°Ð¢&WBÒf–FVôF—7Æ•&÷W'F–W2ÓçWEõF—FÆR‡GF—FÆR“°Ð¢54U%B‡&WBÓÒ5ôô²“°Ð¢ÐÐ¢ÐÐ¢57G&–ær6†FW#°Ð¢–b†Õ÷4"’°Ð¢Etõ$BGt6†6÷VçBÒÕ÷4"Óä6†vWD6÷VçB‚“°Ð¢–b†Gt6†6÷VçB’°Ð¢$TdU$Tä4UõD”ÔR'Dæ÷s°Ð¢Õ÷Õ2ÓävWD7W'&VçE÷6—F–öâ‚g'Dæ÷r“°Ð Ð¢46öÔ%5E"'7G#°Ð¢Æöær7W'&VçD6†ÒÕ÷4"Óä6†Æöö·W‚g'Dæ÷rÂf'7G"“°Ð¢–b†'7G"äÆVæwF‚‚’’°Ð¢6†FW"äf÷&ÖB…õB‚"W2‚VÆBòVÇR’"’Â'7G"æÕ÷7G"Â7FC£¦Ö‚ƒÂÂ7W'&VçD6†²Â’ÂGt6†6÷VçB“°Ð¢ÒVÇ6R°Ð¢6†FW"äf÷&ÖB…õB‚"VÆBòVÇR"’Â7W'&VçD6†²ÂGt6†6÷VçB“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢–b‚6†FW"ä—4V×G’‚’bb6†FW"ÒF—FÆR’°Ð¢…5E$”ärFV×°Ð¢–b…v–æF÷w47&VFU7G&–ær†6†FW"ävWE7G&–ær‚’Â6†FW"ävWDÆVæwF‚‚’ÂgFV×’ÓÒ5ôô²’°Ð¢&WBÒf–FVôF—7Æ•&÷W'F–W2ÓçWEõ7V'F—FÆR‡FV×“°Ð¢54U%B‡&WBÓÒ5ôô²“°Ð¢†fU÷6V6öæF'•÷F—FÆRÒG'VS°Ð¢ÐÐ¢ÐÐ¢–b‚†fU÷6V6öæF'•÷F—FÆRbbWF†÷"ä—4V×G’‚’bbWF†÷"ÒF—FÆR’°Ð¢…5E$”ärFV×°Ð¢–b…v–æF÷w47&VFU7G&–ær†WF†÷"ävWE7G&–ær‚’ÂWF†÷"ävWDÆVæwF‚‚’ÂgFV×’ÓÒ5ôô²’°Ð¢&WBÒf–FVôF—7Æ•&÷W'F–W2ÓçWEõ7V'F—FÆR‡FV×“°Ð¢54U%B‡&WBÓÒ5ôô²“°Ð¢†fU÷6V6öæF'•÷F—FÆRÒG'VS°Ð¢ÐÐ¢Ò Ð¢ÐÐ Ð¢òòF‡VÖ&æ–ÀÐ¢6–bÕ5õ4ÕD5õd”DTõõD…TÔ$ä”ÀÐ¢–b‚ÕödVF–ôöæÇ’’°Ð¢òòf÷"f–FVòÂ66†VGVÆR6GW&–ærf–FVòg&ÖRgFW"Æ–&6²†27F'FVBÀÐ¢òò6VRÖVF–G&ç7÷'D6öçG&öÅWFFUF‡VÖ&æ–Â‚Ð¢ÕöÆ7E4ÕD5F‡VÖ&æ–ÅF–6²Ò°Ð¢ÕöæW‡E4ÕD5F‡VÖ&æ–ÅWFFRÒvWEF–6´6÷VçCcB‚’²STÄÃ°Ð¢ÒVÇ6PÐ¢6VæF–`Ð¢°Ð¢46öÕ•G#Ä”f–ÇFW$w&ƒâf–ÇFW$w&‚ÒÕ÷t#°Ð¢7FC£§fV7F÷#Ä%•DSâ–çFW&æÄ6÷fW#°Ð¢–b„6÷fW$'C£¤f–æDVÖ&VFFVB‡f–ÇFW$w&‚Â–çFW&æÄ6÷fW"’’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂæÆöEF‡VÖ&æ–Â†–çFW&æÄ6÷fW"æFF‚’Â–çFW&æÄ6÷fW"ç6—¦R‚’“°Ð¢ÒVÇ6R°Ð¢5Æ–Æ—7D—FVÒÆ“°Ð¢–b†Õ÷væEÆ–Æ—7D&"ävWD7W"‡Æ’’bbÆ’æÕö6÷fW"ä—4V×G’‚’’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂæÆöEF‡VÖ&æ–Â‡Æ’æÕö6÷fW"“°Ð¢ÒVÇ6R°Ð¢57G&–ærf–ÆVæÖRÒÕ÷væEÆ–Æ—7D&"ävWD7W$f–ÆTæÖR‚“°Ð¢57G&–ærf–ÆVæÖUöæõöW‡C°Ð¢57G&–ærf–ÆVF—#°Ð¢–b‚F…WF–Ç3£¤—5U$Â†f–ÆVæÖR’’°Ð¢5F‚F‚Ò5F‚†f–ÆVæÖR“°Ð¢–b‡F‚äf–ÆTW†—7G2‚’’°Ð¢F‚å&VÖ÷fTW‡FVç6–öâ‚“°Ð¢f–ÆVæÖUöæõöW‡BÒF‚æÕ÷7G%Fƒ°Ð¢F‚å&VÖ÷fTf–ÆU7V2‚“°Ð¢f–ÆVF—"ÒF‚æÕ÷7G%Fƒ°Ð¢&ööÂ—5öf–ÆUö'BÒfÇ6S°Ð¢57G&–ær–ÖrÒ6÷fW$'C£¤f–æDW‡FW&æÂ†f–ÆVæÖUöæõöW‡BÂf–ÆVF—"ÂWF†÷"Â—5öf–ÆUö'B“°Ð¢–b‚–Örä—4V×G’‚’’°Ð¢–b†ÕödVF–ôöæÇ’ÇÂ—5öf–ÆUö'B’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂæÆöEF‡VÖ&æ–Â†–Ör“°Ð¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ¢ÐÐ Ð¢òòWFFRFFæB7FGW0Ð¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEõÆ–&6µ7FGW2„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µ7FGW3£¤ÖVF–Æ–&6µ7FGW5õÆ––ær“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢WEõÆ–&6µ7FGW2W'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓåWFFR‚“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢WFFRW'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ¢òòVæ&ÆPÐ¢&WBÒÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEô—4Væ&ÆVB‡G'VR“°Ð¢–b‡&WBÒ5ôô²’°Ð¢E$4R…õB‚$ÖVF–G&ç46öçG&öÇ3¢WEô—4Væ&ÆVBW'&÷"VÆEÆâ"’Â&WB“°Ð¢&WGW&ã°Ð¢ÐÐ Ð¢òò•7—7FVÔÖVF–G&ç7÷'D6öçG&öÇ3#¢Æ–&6²&FRÂ&WVB÷6‡VffÆR7FFRæBF–ÖVÆ–æPÐ¢ÕöÖVF–÷G&ç5ö6öçG&öÂå6WEÆ–&6µ&FR†ÕöE7VVE&FR“°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂå6WE6‡VffÆTVæ&ÆVB„g„vWD6WGF–æw2‚’æ%6‡VffÆUÆ–Æ—7D—FV×2“°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFTWFõ&WVB‚“°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF–ÖVÆ–æR‡G'VR“°Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅWFFU7FFR„ôf–ÇFW%7FFR7FFR’°Ð¢–b†ÕöÖVF–÷G&ç5ö6öçG&öÂä—47F—fR‚’’°Ð¢–b‡7FFRÓÒ7FFUõ'Vææ–ær’ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEõÆ–&6µ7FGW2„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µ7FGW5õÆ––ær“°Ð¢VÇ6R–b‡7FFRÓÒ7FFUõW6VB’ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEõÆ–&6µ7FGW2„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µ7FGW5õW6VB“°Ð¢VÇ6R–b‡7FFRÓÒ7FFUõ7F÷VB’ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEõÆ–&6µ7FGW2„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µ7FGW5õ7F÷VB“°Ð¢VÇ6RÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ2ÓçWEõÆ–&6µ7FGW2„$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6µ7FGW5ô6†æv–ær“°Ð Ð¢òò¶VW&FRæBF–ÖVÆ–æR–â7–æ2v—F‚F†RæWr7FFRÂ6òF†B6öç7VÖW'0Ð¢òòF†BW‡G&öÆFRF†RÆ–&6²÷6—F–öâ7F’67W&FPÐ¢ÕöÖVF–÷G&ç5ö6öçG&öÂå6WEÆ–&6µ&FR†ÕöE7VVE&FR“°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF–ÖVÆ–æR‡G'VR“°Ð¢6–bÕ5õ4ÕD5õd”DTõõD…TÔ$ä”ÀÐ¢–b‡7FFRÓÒ7FFUõW6VB’°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF‡VÖ&æ–Â‚“°Ð¢ÐÐ¢6VæF–`Ð¢ÐÐ§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅWFFUF–ÖVÆ–æR†&ööÂf÷&6Rò£ÒfÇ6R¢ò’°Ð¢–b‚ÕöÖVF–÷G&ç5ö6öçG&öÂä—47F—fR‚’ÇÂÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5ö6öçG&öÇ3"’°Ð¢&WGW&ã°Ð¢ÐÐ¢òòæ÷FS¢—47F—fR‚’—24ôÒ6ÆÂÂ6òv†VâF‡&÷GFÆ–ær6†V6²F†RF–6²6÷VçBf—'7@Ð¢TÄôätÄôärF–6²ÒvWEF–6´6÷VçCcB‚“°Ð¢–b‚f÷&6RbbF–6²ÂÕöÆ7E4ÕD5F–ÖVÆ–æUWFFR²#TÄÂ’°Ð¢&WGW&ã°Ð¢ÐÐ¢–b„vWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTBÇÂ—5Æ–&6´6GW&TÖöFR‚’ÇÂÕöÖVF–÷G&ç5ö6öçG&öÂä—47F—fR‚’’°Ð¢&WGW&ã°Ð¢ÐÐ¢ÕöÆ7E4ÕD5F–ÖVÆ–æUWFFRÒF–6³°Ð Ð¢õö–çCcB7F'BÒÂ7F÷Ò°Ð¢Õ÷væE6VV´&"ävWE&ævR‡7F'BÂ7F÷“°Ð¢–b‡7F÷â’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂåWFFUF–ÖVÆ–æU&÷W'F–W2ƒÂ7F÷ÂÕ÷væE6VV´&"ävWE÷2‚’“°Ð¢ÐÐ Ð¢6–bÕ5õ4ÕD5õd”DTõõD…TÔ$ä”ÀÐ¢òòW&–öF–2F‡VÖ&æ–Â&Vg&W6‚ÂG&—fVâg&öÒF†R6ÖRF‡&÷GFÆVBF€Ð¢–b†ÕöæW‡E4ÕD5F‡VÖ&æ–ÅWFFRbbF–6²ãÒÕöæW‡E4ÕD5F‡VÖ&æ–ÅWFFRbbvWDÖVF–7FFR‚’ÓÒ7FFUõ'Vææ–ær’°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFUF‡VÖ&æ–Â‚“°Ð¢ÐÐ¢6VæF–`Ð§ÐÐ Ð§fö–B4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅWFFTWFõ&WVB‚’°Ð¢6öç7B46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFRÖöFRÒ$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFUôæöæS°Ð¢–b‡2ædÆö÷f÷&WfW"’°Ð¢ÖöFRÒ‡2æTÆö÷ÖöFRÓÒ46WGF–æw3£¤Æö÷ÖöFS£¤d”ÄR’ò$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFUõG&6°Ð¢¢$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFUôÆ—7C°Ð¢ÐÐ¢ÕöÖVF–÷G&ç5ö6öçG&öÂå6WDWFõ&WVDÖöFR†ÖöFR“°Ð§ÐÐ Ð¢6–bÕ5õ4ÕD5õd”DTõõD…TÔ$ä”ÀÐ§fö–B4Ö–äg&ÖS£¤ÖVF–G&ç7÷'D6öçG&öÅWFFUF‡VÖ&æ–Â‚’°Ð¢–b†ÕödVF–ôöæÇ’ÇÂvWDÆöE7FFR‚’ÒÔÅ3£¤ÄôDTBÇÂ—5Æ–&6´6GW&TÖöFR‚’ÇÂÕöÖVF–÷G&ç5ö6öçG&öÂä—47F—fR‚’’°Ð¢&WGW&ã°Ð¢ÐÐ¢òò6GW&RBÖ÷7Böæ6RW"6V6öæBÂRærâv†Vâ6VV¶–ær&WVFVFÇÐ¢TÄôätÄôärF–6²ÒvWEF–6´6÷VçCcB‚“°Ð¢–b†ÕöÆ7E4ÕD5F‡VÖ&æ–ÅF–6²bbF–6²ÂÕöÆ7E4ÕD5F‡VÖ&æ–ÅF–6²²TÄÂ’°Ð¢&WGW&ã°Ð¢ÐÐ¢ÕöÆ7E4ÕD5F‡VÖ&æ–ÅF–6²ÒF–6³°Ð¢ÕöæW‡E4ÕD5F‡VÖ&æ–ÅWFFRÒF–6²²3TÄÃ°Ð Ð¢7FC£§fV7F÷#Ä%•DSâF‡VÖ&æ–Ã°Ð¢–b„6GW&Uf–FVõF‡VÖ&æ–Â‡F‡VÖ&æ–Â’’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂæÆöEF‡VÖ&æ–Â‡F‡VÖ&æ–ÂæFF‚’ÂF‡VÖ&æ–Âç6—¦R‚’“°Ð¢–b†ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"’°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂç6×F5÷WFFW"ÓåWFFR‚“°Ð¢ÐÐ¢ÐÐ§ÐÐ¢6VæF–`Ð Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öå6×F56VV²…u$Òu&ÒÂÅ$ÒÅ&Ò’°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbb—5Æ–&6´6GW&TÖöFR‚’’°Ð¢6VVµFò†ÕöÖVF–÷G&ç5ö6öçG&öÂç&WVW7FVE÷6VVµ÷÷6—F–öâÂfÇ6R“°Ð¢ÐÐ¢&WGW&â°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öå6×F4WFõ&WVB…u$Òu&ÒÂÅ$ÒÅ&Ò’°Ð¢46WGF–æw2b2Òg„vWD6WGF–æw2‚“°Ð¢WFòÖöFRÒ7FF–5ö67CÄ$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFSâ‡u&Ò“°Ð¢7v—F6‚†ÖöFR’°Ð¢66R$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFUõG&6³ Ð¢2ædÆö÷f÷&WfW"ÒG'VS°Ð¢2æTÆö÷ÖöFRÒ46WGF–æw3£¤Æö÷ÖöFS£¤d”ÄS°Ð¢'&V³°Ð¢66R$“£¥v–æF÷w3£¤ÖVF–£¤ÖVF–Æ–&6´WFõ&WVDÖöFUôÆ—7C Ð¢2ædÆö÷f÷&WfW"ÒG'VS°Ð¢2æTÆö÷ÖöFRÒ46WGF–æw3£¤Æö÷ÖöFS£¥Ä”Ä•5C°Ð¢'&V³°Ð¢FVfVÇC Ð¢2ædÆö÷f÷&WfW"ÒfÇ6S°Ð¢'&V³°Ð¢ÐÐ¢ÕöäÆö÷2Ò°Ð¢ÖVF–G&ç7÷'D6öçG&öÅWFFTWFõ&WVB‚“°Ð¢&WGW&â°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öå6×F56‡VffÆR…u$Òu&ÒÂÅ$ÒÅ&Ò’°Ð¢–b„g„vWD6WGF–æw2‚’æ%6‡VffÆUÆ–Æ—7D—FV×2Ò‡u&ÒÒ’’°Ð¢öåÆ–Æ—7EFövvÆU6‡VffÆR‚“°Ð¢ÒVÇ6R°Ð¢ÕöÖVF–÷G&ç5ö6öçG&öÂå6WE6‡VffÆTVæ&ÆVB‡u&ÒÒ“°Ð¢ÐÐ¢&WGW&â°Ð§ÐÐ Ð¤Å$U5TÅB4Ö–äg&ÖS£¤öå6×F5&FR…u$Òu&ÒÂÅ$ÒÅ&Ò’°Ð¢F÷V&ÆR&FRÒÕöÖVF–÷G&ç5ö6öçG&öÂç&WVW7FVE÷Æ–&6µ÷&FS°Ð¢–b„vWDÆöE7FFR‚’ÓÒÔÅ3£¤ÄôDTBbb&FRâã’°Ð¢6WEÆ––æu&FR‡&FR“°Ð¢ÐÐ¢&WGW&â°Ð§ÐÐ 