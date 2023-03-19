include "wcel.mm"
include "wss.mm"
include "wnel.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "simp2.mm"
include "sselda.mm"
include "wn.mm"
include "df-nel.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "anim1i.mm"
include "ancomd.mm"
include "nelne2.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "wb.mm"
include "elpwg.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem elpwdifsn
  let cA: class A
  let cS: class S
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( S e. W /\ S C_ V /\ A e/ S ) -> S e. ~P ( V \ { A } ) )

  proof
    cS
    cW
    wcel
    #
    cS
    cV
    wss
    #
    cA
    cS
    wnel
    #
    w3a
    #
    cS
    cV
    cA
    csn
    cdif
    #
    cpw
    wcel
    #
    cS
    @4
    wss
    #
    @3
    vx
    cS
    @4
    @3
    vx
    cv
    #
    cS
    wcel
    #
    @7
    @4
    wcel
    #
    @3
    @8
    wa
    #
    @7
    cV
    wcel
    @7
    cA
    wne
    #
    @9
    @3
    cS
    cV
    @7
    @0
    @1
    @2
    simp2
    sselda
    @10
    @8
    cA
    cS
    wcel
    wn
    #
    wa
    @11
    @10
    @12
    @8
    @3
    @12
    @8
    @2
    @0
    @12
    @1
    @2
    @12
    cA
    cS
    df-nel
    biimpi
    3ad2ant3
    anim1i
    ancomd
    @7
    cA
    cS
    nelne2
    syl
    @7
    cV
    cA
    eldifsn
    sylanbrc
    ex
    ssrdv
    @0
    @1
    @5
    @6
    wb
    @2
    cS
    @4
    cW
    elpwg
    3ad2ant1
    mpbird
end
