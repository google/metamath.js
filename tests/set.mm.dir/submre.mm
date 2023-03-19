include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "simpr.mm"
include "pwidg.mm"
include "adantl.mm"
include "elind.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "simp1l.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "mreintcl.mm"
include "syl3anc.mm"
include "cuni.mm"
include "intssuni2.mm"
include "syl2anc.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "wb.mm"
include "elpw2g.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "ismred.mm"

theorem submre
  let cA: class A
  let cC: class C
  let cX: class X
  let vx: setvar x


  assert |- ( ( C e. ( Moore ` X ) /\ A e. C ) -> ( C i^i ~P A ) e. ( Moore ` A ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cA
    cC
    wcel
    #
    wa
    #
    cC
    cA
    cpw
    #
    cin
    #
    cA
    vx
    @4
    @3
    wss
    #
    @2
    cC
    @3
    inss2
    #
    a1i
    @2
    cC
    @3
    cA
    @0
    @1
    simpr
    @1
    cA
    @3
    wcel
    @0
    cA
    cC
    pwidg
    adantl
    elind
    @2
    vx
    cv
    #
    @4
    wss
    #
    @7
    c0
    wne
    #
    w3a
    #
    cC
    @3
    @7
    cint
    #
    @10
    @0
    @7
    cC
    wss
    #
    @9
    @11
    cC
    wcel
    @0
    @1
    @8
    @9
    simp1l
    @8
    @2
    @12
    @9
    @8
    @4
    cC
    wss
    @12
    cC
    @3
    inss1
    @7
    @4
    cC
    sstr
    mpan2
    3ad2ant2
    @2
    @8
    @9
    simp3
    #
    cC
    @7
    cX
    mreintcl
    syl3anc
    @10
    @11
    @3
    wcel
    #
    @11
    cA
    wss
    #
    @10
    @11
    @3
    cuni
    #
    cA
    @10
    @7
    @3
    wss
    #
    @9
    @11
    @16
    wss
    @8
    @2
    @17
    @9
    @8
    @5
    @17
    @6
    @7
    @4
    @3
    sstr
    mpan2
    3ad2ant2
    @13
    @7
    @3
    intssuni2
    syl2anc
    cA
    unipw
    syl6sseq
    @2
    @8
    @14
    @15
    wb
    #
    @9
    @1
    @18
    @0
    @11
    cA
    cC
    elpw2g
    adantl
    3ad2ant1
    mpbird
    elind
    ismred
end
