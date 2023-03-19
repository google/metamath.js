include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "cfv.mm"
include "wpss.mm"
include "wi.mm"
include "elnn.mm"
include "ancoms.mm"
include "csuc.mm"
include "word.mm"
include "nnord.mm"
include "ordsucss.mm"
include "syl.mm"
include "adantr.mm"
include "peano2b.mm"
include "wceq.mm"
include "fveq2.mm"
include "psseq2d.mm"
include "imbi2d.mm"
include "inf3lem4.mm"
include "com12.mm"
include "sylbir.mm"
include "vex.mm"
include "psstr.mm"
include "expcom.mm"
include "syl6com.mm"
include "a2d.mm"
include "ad2antrr.mm"
include "findsg.mm"
include "ex.mm"
include "sylan2b.mm"
include "syld.mm"
include "impancom.mm"
include "mpd.mm"

theorem inf3lem5
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> ( ( A e. _om /\ B e. A ) -> ( F ` B ) C. ( F ` A ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    vx
    cv
    #
    c0
    wne
    @3
    @3
    cuni
    wss
    wa
    #
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    wpss
    #
    @2
    cB
    com
    wcel
    #
    @4
    @7
    wi
    #
    @1
    @0
    @8
    cB
    cA
    elnn
    ancoms
    @0
    @8
    @1
    @9
    @0
    @8
    wa
    @1
    cB
    csuc
    #
    cA
    wss
    #
    @9
    @0
    @1
    @11
    wi
    #
    @8
    @0
    cA
    word
    @12
    cA
    nnord
    cB
    cA
    ordsucss
    syl
    adantr
    @8
    @0
    @10
    com
    wcel
    #
    @11
    @9
    wi
    cB
    peano2b
    #
    @0
    @13
    wa
    @11
    @9
    @4
    @5
    vv
    cv
    #
    cF
    cfv
    #
    wpss
    #
    wi
    @4
    @5
    @10
    cF
    cfv
    #
    wpss
    #
    wi
    #
    @4
    @5
    vu
    cv
    #
    cF
    cfv
    #
    wpss
    #
    wi
    #
    @4
    @5
    @21
    csuc
    #
    cF
    cfv
    #
    wpss
    #
    wi
    #
    @9
    vv
    vu
    cA
    @10
    @15
    @10
    wceq
    #
    @17
    @19
    @4
    @29
    @16
    @18
    @5
    @15
    @10
    cF
    fveq2
    psseq2d
    imbi2d
    @15
    @21
    wceq
    #
    @17
    @23
    @4
    @30
    @16
    @22
    @5
    @15
    @21
    cF
    fveq2
    psseq2d
    imbi2d
    @15
    @25
    wceq
    #
    @17
    @27
    @4
    @31
    @16
    @26
    @5
    @15
    @25
    cF
    fveq2
    psseq2d
    imbi2d
    @15
    cA
    wceq
    #
    @17
    @7
    @4
    @32
    @16
    @6
    @5
    @15
    cA
    cF
    fveq2
    psseq2d
    imbi2d
    @13
    @8
    @20
    @14
    @4
    @8
    @19
    vx
    vy
    vw
    cB
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.4
    inf3lem.4
    inf3lem4
    com12
    sylbir
    @21
    com
    wcel
    #
    @24
    @28
    wi
    @13
    @10
    @21
    wss
    @33
    @4
    @23
    @27
    @4
    @33
    @22
    @26
    wpss
    #
    @23
    @27
    wi
    vx
    vy
    vw
    @21
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    vu
    vex
    inf3lem.4
    inf3lem4
    @23
    @34
    @27
    @5
    @22
    @26
    psstr
    expcom
    syl6com
    a2d
    ad2antrr
    findsg
    ex
    sylan2b
    syld
    impancom
    mpd
    com12
end
