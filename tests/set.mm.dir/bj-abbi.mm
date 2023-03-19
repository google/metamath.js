include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "dfcleq.mm"
include "bj-nfsab1.mm"
include "nfbi.mm"
include "nfv.mm"
include "weq.mm"
include "wsb.mm"
include "df-clab.mm"
include "sbequ12r.mm"
include "syl5bb.mm"
include "bibi12d.mm"
include "cbvalv1.mm"
include "bitr2i.mm"

theorem bj-abbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph <-> ps ) <-> { x | ph } = { x | ps } )

  proof
    wph
    vx
    cab
    #
    wps
    vx
    cab
    #
    wceq
    vy
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wb
    #
    vy
    wal
    wph
    wps
    wb
    #
    vx
    wal
    vy
    @0
    @1
    dfcleq
    @5
    @6
    vy
    vx
    @3
    @4
    vx
    wph
    vx
    vy
    bj-nfsab1
    wps
    vx
    vy
    bj-nfsab1
    nfbi
    @6
    vy
    nfv
    vy
    vx
    weq
    #
    @3
    wph
    @4
    wps
    @3
    wph
    vx
    vy
    wsb
    @7
    wph
    wph
    vy
    vx
    df-clab
    wph
    vy
    vx
    sbequ12r
    syl5bb
    @4
    wps
    vx
    vy
    wsb
    @7
    wps
    wps
    vy
    vx
    df-clab
    wps
    vy
    vx
    sbequ12r
    syl5bb
    bibi12d
    cbvalv1
    bitr2i
end
