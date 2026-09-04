/*
 * Tablet-style frame used by the custom MPC-HC build.
 *
 * This file is part of MPC-HC and is distributed under the terms of the
 * GNU General Public License version 3 or (at your option) any later version.
 */

#pragma once

class CTabletFrameWnd final : public CWnd
{
public:
    BOOL Create(CWnd* pOwner);
    void SyncToOwner(bool showFrame = true);

protected:
    DECLARE_MESSAGE_MAP()

    afx_msg void OnPaint();
    afx_msg BOOL OnEraseBkgnd(CDC* pDC);
    afx_msg void OnLButtonDown(UINT nFlags, CPoint point);
    afx_msg BOOL OnSetCursor(CWnd* pWnd, UINT nHitTest, UINT message);

private:
    CWnd* m_pOwner = nullptr;
    int m_scale = 100;
    int m_bezel = 12;
    int m_hardwareHeight = 9;
    int m_cornerRadius = 30;
    int m_strokeWidth = 2;
    int m_ownerInsetLeft = 0;
    int m_ownerInsetRight = 0;
    int m_ownerInsetBottom = 0;

    CRect m_volumeButtonRect;
    CRect m_playButtonRect;

    int Scale(int value) const;
    void UpdateMetrics();
    void RebuildWindowRegion();
    UINT ResizeHitTest(CPoint point) const;
    void ForwardResizeOrMove(UINT hitTest, CPoint point);
};
