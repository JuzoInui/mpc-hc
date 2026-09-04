/*
 * Tablet-style frame used by the custom MPC-HC build.
 *
 * This file is part of MPC-HC and is distributed under the terms of the
 * GNU General Public License version 3 or (at your option) any later version.
 */

#include "stdafx.h"
#include "TabletFrameWnd.h"
#include "resource.h"

BEGIN_MESSAGE_MAP(CTabletFrameWnd, CWnd)
    ON_WM_PAINT()
    ON_WM_ERASEBKGND()
    ON_WM_LBUTTONDOWN()
    ON_WM_SETCURSOR()
END_MESSAGE_MAP()

namespace {
constexpr COLORREF kBodyColor = RGB(18, 20, 24);
constexpr COLORREF kOuterStrokeColor = RGB(218, 220, 223);
constexpr COLORREF kInnerStrokeColor = RGB(57, 61, 68);
constexpr COLORREF kBezelHighlightColor = RGB(92, 97, 105);
constexpr COLORREF kButtonFaceColor = RGB(83, 87, 94);
constexpr COLORREF kButtonHighlightColor = RGB(196, 199, 204);
constexpr COLORREF kCameraColor = RGB(8, 10, 13);
}

BOOL CTabletFrameWnd::Create(CWnd* pOwner)
{
    ASSERT_VALID(pOwner);
    m_pOwner = pOwner;

    const CString className = AfxRegisterWndClass(
        CS_HREDRAW | CS_VREDRAW | CS_DBLCLKS,
        ::LoadCursor(nullptr, IDC_ARROW),
        nullptr,
        nullptr);

    return CreateEx(
        WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE,
        className,
        _T("MPC-HC tablet frame"),
        WS_POPUP,
        CRect(0, 0, 0, 0),
        pOwner,
        0);
}

int CTabletFrameWnd::Scale(int value) const
{
    return MulDiv(value, m_scale, 100);
}

void CTabletFrameWnd::UpdateMetrics()
{
    HDC hdc = ::GetDC(m_pOwner->GetSafeHwnd());
    const int dpi = hdc ? GetDeviceCaps(hdc, LOGPIXELSX) : 96;
    if (hdc) {
        ::ReleaseDC(m_pOwner->GetSafeHwnd(), hdc);
    }

    m_scale = MulDiv(dpi, 100, 96);
    m_bezel = Scale(20);
    m_hardwareHeight = Scale(9);
    m_cornerRadius = Scale(30);
    m_strokeWidth = std::max(1, Scale(2));
}

void CTabletFrameWnd::SyncToOwner(bool showFrame)
{
    if (!::IsWindow(GetSafeHwnd()) || !m_pOwner || !::IsWindow(m_pOwner->GetSafeHwnd())) {
        return;
    }

    const HWND owner = m_pOwner->GetSafeHwnd();
    if (!showFrame || !::IsWindowVisible(owner) || ::IsIconic(owner) || ::IsZoomed(owner)) {
        ShowWindow(SW_HIDE);
        return;
    }

    UpdateMetrics();

    CRect ownerRect;
    m_pOwner->GetWindowRect(ownerRect);
    const CRect frameRect(
        ownerRect.left - m_bezel,
        ownerRect.top - m_bezel - m_hardwareHeight,
        ownerRect.right + m_bezel,
        ownerRect.bottom + m_bezel);

    SetWindowPos(
        &wndTop,
        frameRect.left,
        frameRect.top,
        frameRect.Width(),
        frameRect.Height(),
        SWP_NOACTIVATE | SWP_SHOWWINDOW);

    RebuildWindowRegion();
    Invalidate(FALSE);
}

void CTabletFrameWnd::RebuildWindowRegion()
{
    CRect clientRect;
    GetClientRect(clientRect);
    if (clientRect.IsRectEmpty()) {
        return;
    }

    const int buttonTop = 0;
    const int bodyTop = m_hardwareHeight;
    const int buttonBottom = bodyTop + Scale(5);
    const int buttonLeft = m_bezel + Scale(82);

    m_volumeButtonRect.SetRect(buttonLeft, buttonTop, buttonLeft + Scale(76), buttonBottom);
    m_playButtonRect.SetRect(buttonLeft + Scale(108), buttonTop, buttonLeft + Scale(160), buttonBottom);

    CRgn windowRegion;
    windowRegion.CreateRoundRectRgn(
        0,
        bodyTop,
        clientRect.right + 1,
        clientRect.bottom + 1,
        m_cornerRadius * 2,
        m_cornerRadius * 2);

    CRgn centerHole;
    centerHole.CreateRoundRectRgn(
        m_bezel,
        bodyTop + m_bezel,
        clientRect.right - m_bezel + 1,
        clientRect.bottom - m_bezel + 1,
        Scale(11),
        Scale(11));
    windowRegion.CombineRgn(&windowRegion, &centerHole, RGN_DIFF);

    CRgn volumeButton;
    volumeButton.CreateRoundRectRgn(
        m_volumeButtonRect.left,
        m_volumeButtonRect.top,
        m_volumeButtonRect.right + 1,
        m_volumeButtonRect.bottom + 1,
        Scale(5),
        Scale(5));
    windowRegion.CombineRgn(&windowRegion, &volumeButton, RGN_OR);

    CRgn playButton;
    playButton.CreateRoundRectRgn(
        m_playButtonRect.left,
        m_playButtonRect.top,
        m_playButtonRect.right + 1,
        m_playButtonRect.bottom + 1,
        Scale(5),
        Scale(5));
    windowRegion.CombineRgn(&windowRegion, &playButton, RGN_OR);

    SetWindowRgn(static_cast<HRGN>(windowRegion.Detach()), TRUE);
}

void CTabletFrameWnd::OnPaint()
{
    CPaintDC dc(this);
    CRect clientRect;
    GetClientRect(clientRect);

    CRgn clipRegion;
    clipRegion.CreateRectRgn(0, 0, 0, 0);
    if (GetWindowRgn(static_cast<HRGN>(clipRegion.GetSafeHandle())) != ERROR) {
        CBrush bodyBrush(kBodyColor);
        dc.FillRgn(&clipRegion, &bodyBrush);
    }

    const int oldBkMode = dc.SetBkMode(TRANSPARENT);
    CBrush bodyBrush(kBodyColor);
    CBrush buttonBrush(kButtonFaceColor);
    CPen outerPen(PS_SOLID, m_strokeWidth, kOuterStrokeColor);
    CPen innerPen(PS_SOLID, std::max(1, m_strokeWidth / 2), kInnerStrokeColor);
    CPen bezelHighlightPen(PS_SOLID, std::max(1, Scale(1)), kBezelHighlightColor);
    CPen buttonPen(PS_SOLID, std::max(1, m_strokeWidth / 2), kButtonHighlightColor);

    CPen* oldPen = dc.SelectObject(&outerPen);
    CBrush* oldBrush = dc.SelectObject(&bodyBrush);
    dc.RoundRect(
        CRect(1, m_hardwareHeight + 1, clientRect.right - 1, clientRect.bottom - 1),
        CPoint(m_cornerRadius * 2, m_cornerRadius * 2));

    dc.SelectObject(&bezelHighlightPen);
    dc.SelectStockObject(NULL_BRUSH);
    dc.RoundRect(
        CRect(Scale(4), m_hardwareHeight + Scale(4), clientRect.right - Scale(4), clientRect.bottom - Scale(4)),
        CPoint((m_cornerRadius - Scale(4)) * 2, (m_cornerRadius - Scale(4)) * 2));

    dc.SelectObject(&innerPen);
    dc.SelectStockObject(NULL_BRUSH);
    dc.RoundRect(CRect(
        m_bezel - 1,
        m_hardwareHeight + m_bezel - 1,
        clientRect.right - m_bezel + 1,
        clientRect.bottom - m_bezel + 1),
        CPoint(Scale(11), Scale(11)));

    // Small camera and speaker details make the bezel read as a physical
    // tablet instead of a generic rounded window border.
    CBrush cameraBrush(kCameraColor);
    dc.SelectObject(&cameraBrush);
    dc.Ellipse(CRect(
        clientRect.right - m_bezel / 2 - Scale(3),
        clientRect.CenterPoint().y - Scale(3),
        clientRect.right - m_bezel / 2 + Scale(3),
        clientRect.CenterPoint().y + Scale(3)));
    dc.RoundRect(CRect(
        m_bezel / 2 - Scale(2),
        clientRect.CenterPoint().y - Scale(22),
        m_bezel / 2 + Scale(2),
        clientRect.CenterPoint().y + Scale(22)),
        CPoint(Scale(3), Scale(3)));

    dc.SelectObject(&buttonPen);
    dc.SelectObject(&buttonBrush);
    dc.RoundRect(m_volumeButtonRect, CPoint(Scale(5), Scale(5)));
    dc.RoundRect(m_playButtonRect, CPoint(Scale(5), Scale(5)));

    const int dividerX = m_volumeButtonRect.CenterPoint().x;
    dc.MoveTo(dividerX, m_volumeButtonRect.top + Scale(2));
    dc.LineTo(dividerX, m_volumeButtonRect.bottom - Scale(2));

    dc.SelectObject(oldBrush);
    dc.SelectObject(oldPen);
    dc.SetBkMode(oldBkMode);
}

BOOL CTabletFrameWnd::OnEraseBkgnd(CDC* pDC)
{
    UNREFERENCED_PARAMETER(pDC);
    return TRUE;
}

UINT CTabletFrameWnd::ResizeHitTest(CPoint point) const
{
    CRect clientRect;
    GetClientRect(clientRect);

    const bool left = point.x < m_bezel;
    const bool right = point.x >= clientRect.right - m_bezel;
    // Keep most of the upper bezel draggable while reserving its outer edge
    // for vertical resizing.
    const bool top = point.y >= m_hardwareHeight
                     && point.y < m_hardwareHeight + Scale(5);
    const bool bottom = point.y >= clientRect.bottom - m_bezel;

    if (top && left) return HTTOPLEFT;
    if (top && right) return HTTOPRIGHT;
    if (bottom && left) return HTBOTTOMLEFT;
    if (bottom && right) return HTBOTTOMRIGHT;
    if (left) return HTLEFT;
    if (right) return HTRIGHT;
    if (bottom) return HTBOTTOM;
    if (top) return HTTOP;
    return HTCAPTION;
}

void CTabletFrameWnd::ForwardResizeOrMove(UINT hitTest, CPoint point)
{
    ClientToScreen(&point);
    m_pOwner->SetForegroundWindow();
    m_pOwner->SendMessage(WM_NCLBUTTONDOWN, hitTest, MAKELPARAM(point.x, point.y));
}

void CTabletFrameWnd::OnLButtonDown(UINT nFlags, CPoint point)
{
    if (m_volumeButtonRect.PtInRect(point)) {
        const UINT command = point.x < m_volumeButtonRect.CenterPoint().x ? ID_VOLUME_DOWN : ID_VOLUME_UP;
        m_pOwner->PostMessage(WM_COMMAND, command);
        return;
    }

    if (m_playButtonRect.PtInRect(point)) {
        m_pOwner->PostMessage(WM_COMMAND, ID_PLAY_PLAYPAUSE);
        return;
    }

    ForwardResizeOrMove(ResizeHitTest(point), point);
    __super::OnLButtonDown(nFlags, point);
}

BOOL CTabletFrameWnd::OnSetCursor(CWnd* pWnd, UINT nHitTest, UINT message)
{
    CPoint point;
    GetCursorPos(&point);
    ScreenToClient(&point);

    if (m_volumeButtonRect.PtInRect(point) || m_playButtonRect.PtInRect(point)) {
        ::SetCursor(AfxGetApp()->LoadStandardCursor(IDC_HAND));
        return TRUE;
    }

    LPCTSTR cursor = IDC_ARROW;
    switch (ResizeHitTest(point)) {
        case HTLEFT:
        case HTRIGHT: cursor = IDC_SIZEWE; break;
        case HTTOP:
        case HTBOTTOM: cursor = IDC_SIZENS; break;
        case HTTOPLEFT:
        case HTBOTTOMRIGHT: cursor = IDC_SIZENWSE; break;
        case HTTOPRIGHT:
        case HTBOTTOMLEFT: cursor = IDC_SIZENESW; break;
    }
    ::SetCursor(AfxGetApp()->LoadStandardCursor(cursor));
    return TRUE;
}
