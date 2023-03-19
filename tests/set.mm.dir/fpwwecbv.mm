include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "copab.mm"
include "weq.mm"
include "simpl.mm"
include "sseq1d.mm"
include "simpr.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "cbvopabv.mm"
include "eqtri.mm"

theorem fpwwecbv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vu: setvar u
  let wph: wff ph
  let cR: class R
  let cX: class X
  let cY: class Y
  assume fpwwe.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) }

  disjoint a r
  disjoint a s
  disjoint a x
  disjoint A a
  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a u
  disjoint r u
  disjoint s u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint ph r
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint R r
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint X r
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint Y r
  disjoint Y u
  disjoint Y x
  disjoint Y y
  assert |- W = { <. a , s >. | ( ( a C_ A /\ s C_ ( a X. a ) ) /\ ( s We a /\ A. z e. a ( F ` ( `' s " { z } ) ) = z ) ) }

  proof
    cW
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @0
    @0
    cxp
    #
    wss
    #
    wa
    #
    @0
    @2
    wwe
    #
    @2
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    cF
    cfv
    #
    @8
    wceq
    #
    vy
    @0
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    copab
    va
    cv
    #
    cA
    wss
    #
    vs
    cv
    #
    @16
    @16
    cxp
    #
    wss
    #
    wa
    #
    @16
    @18
    wwe
    #
    @18
    ccnv
    #
    vz
    cv
    #
    csn
    #
    cima
    #
    cF
    cfv
    #
    @24
    wceq
    #
    vz
    @16
    wral
    #
    wa
    #
    wa
    #
    va
    vs
    copab
    fpwwe.1
    @15
    @31
    vx
    vr
    va
    vs
    vx
    va
    weq
    #
    vr
    vs
    weq
    #
    wa
    #
    @5
    @21
    @14
    @30
    @34
    @1
    @17
    @4
    @20
    @34
    @0
    @16
    cA
    @32
    @33
    simpl
    #
    sseq1d
    @34
    @2
    @18
    @3
    @19
    @32
    @33
    simpr
    #
    @34
    @0
    @16
    @35
    sqxpeqd
    sseq12d
    anbi12d
    @34
    @6
    @22
    @13
    @29
    @32
    @6
    @16
    @2
    wwe
    @33
    @22
    @0
    @16
    @2
    weeq2
    @16
    @2
    @18
    weeq1
    sylan9bb
    @13
    @7
    @25
    cima
    #
    cF
    cfv
    #
    @24
    wceq
    #
    vz
    @0
    wral
    @34
    @29
    @12
    @39
    vy
    vz
    @0
    vy
    vz
    weq
    #
    @11
    @38
    @8
    @24
    @40
    @10
    @37
    cF
    @40
    @9
    @25
    @7
    @8
    @24
    sneq
    imaeq2d
    fveq2d
    @40
    id
    eqeq12d
    cbvralv
    @34
    @39
    @28
    vz
    @0
    @16
    @35
    @34
    @38
    @27
    @24
    @34
    @37
    @26
    cF
    @34
    @7
    @23
    @25
    @34
    @2
    @18
    @36
    cnveqd
    imaeq1d
    fveq2d
    eqeq1d
    raleqbidv
    syl5bb
    anbi12d
    anbi12d
    cbvopabv
    eqtri
end
