include "c0.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "wnel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wal.mm"
include "ianor.mm"
include "bicomi.mm"
include "albii.mm"
include "alnex.mm"
include "bitri.mm"
include "vex.mm"
include "prnz.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "alrimivv.mm"
include "2nexaln.mm"
include "sylibr.mm"
include "imori.mm"
include "mpgbi.mm"
include "wcel.mm"
include "df-nel.mm"
include "clelab.mm"
include "xchbinx.mm"
include "mpbir.mm"

theorem spr0nelg
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint a p
  disjoint b p
  disjoint k x
  assert |- (/) e/ { p | E. a E. b p = { a , b } }

  proof
    c0
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    wex
    va
    wex
    #
    vp
    cab
    #
    wnel
    #
    @0
    c0
    wceq
    #
    @5
    wa
    #
    vp
    wex
    #
    wn
    #
    @8
    wn
    @5
    wn
    #
    wo
    #
    @11
    vp
    @13
    vp
    wal
    @9
    wn
    #
    vp
    wal
    @11
    @13
    @14
    vp
    @14
    @13
    @8
    @5
    ianor
    bicomi
    albii
    @9
    vp
    alnex
    bitri
    @8
    @12
    @8
    @4
    wn
    #
    vb
    wal
    va
    wal
    @12
    @8
    @15
    va
    vb
    @8
    @4
    c0
    @3
    wceq
    @3
    c0
    @1
    @2
    va
    vex
    prnz
    nesymi
    @0
    c0
    @3
    eqeq1
    mtbiri
    alrimivv
    @4
    va
    vb
    2nexaln
    sylibr
    imori
    mpgbi
    @7
    c0
    @6
    wcel
    @10
    c0
    @6
    df-nel
    @5
    vp
    c0
    clelab
    xchbinx
    mpbir
end
