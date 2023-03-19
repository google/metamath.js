include "cv.mm"
include "wcel.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "wbr.mm"
include "wi.mm"
include "vex.mm"
include "tfrlem3a.mm"
include "reeanv.mm"
include "w3a.mm"
include "cin.mm"
include "simp2ll.mm"
include "simp3l.mm"
include "fnbr.mm"
include "syl2anc.mm"
include "simp2rl.mm"
include "simp3r.mm"
include "elind.mm"
include "onin.mm"
include "3ad2ant1.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "fnfun.mm"
include "syl.mm"
include "inss1.mm"
include "fndm.mm"
include "syl5sseqr.mm"
include "jca.mm"
include "inss2.mm"
include "simp2lr.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "simp2rr.mm"
include "tfrlem1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "funbrfv.mm"
include "3eqtr3d.mm"
include "3exp.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem tfrlem5
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint F f
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint A g
  disjoint A h
  disjoint f z
  disjoint B f
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint h z
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A z
  assert |- ( ( g e. A /\ h e. A ) -> ( ( x g u /\ x h v ) -> u = v ) )

  proof
    vg
    cv
    #
    cA
    wcel
    @0
    vz
    cv
    #
    wfn
    #
    va
    cv
    #
    @0
    cfv
    #
    @0
    @3
    cres
    cF
    cfv
    wceq
    #
    va
    @1
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    vh
    cv
    #
    vw
    cv
    #
    wfn
    #
    @3
    @9
    cfv
    #
    @9
    @3
    cres
    cF
    cfv
    wceq
    #
    va
    @10
    wral
    #
    wa
    #
    vw
    con0
    wrex
    #
    vx
    cv
    #
    vu
    cv
    #
    @0
    wbr
    #
    @17
    vv
    cv
    #
    @9
    wbr
    #
    wa
    #
    @18
    @20
    wceq
    #
    wi
    #
    @9
    cA
    wcel
    vx
    vy
    vz
    va
    cA
    vf
    cF
    @0
    tfrlem.1
    vg
    vex
    tfrlem3a
    vx
    vy
    vw
    va
    cA
    vf
    cF
    @9
    tfrlem.1
    vh
    vex
    tfrlem3a
    @8
    @16
    wa
    @7
    @15
    wa
    #
    vw
    con0
    wrex
    vz
    con0
    wrex
    @24
    @7
    @15
    vz
    vw
    con0
    con0
    reeanv
    @25
    @24
    vz
    vw
    con0
    con0
    @1
    con0
    wcel
    @10
    con0
    wcel
    wa
    #
    @25
    @22
    @23
    @26
    @25
    @22
    w3a
    #
    @17
    @0
    cfv
    #
    @17
    @9
    cfv
    #
    @18
    @20
    @27
    @17
    @1
    @10
    cin
    #
    wcel
    @4
    @12
    wceq
    #
    va
    @30
    wral
    @28
    @29
    wceq
    #
    @27
    @1
    @10
    @17
    @27
    @2
    @19
    @17
    @1
    wcel
    @2
    @6
    @15
    @26
    @22
    simp2ll
    #
    @26
    @25
    @19
    @21
    simp3l
    #
    @1
    @17
    @18
    @0
    fnbr
    syl2anc
    @27
    @11
    @21
    @17
    @10
    wcel
    @11
    @14
    @7
    @26
    @22
    simp2rl
    #
    @26
    @25
    @19
    @21
    simp3r
    #
    @10
    @17
    @20
    @9
    fnbr
    syl2anc
    elind
    @27
    va
    @30
    cF
    @0
    @9
    @26
    @25
    @30
    con0
    wcel
    @22
    @1
    @10
    onin
    3ad2ant1
    @27
    @0
    wfun
    #
    @30
    @0
    cdm
    #
    wss
    @27
    @2
    @37
    @33
    @1
    @0
    fnfun
    syl
    #
    @27
    @1
    @30
    @38
    @1
    @10
    inss1
    #
    @27
    @2
    @38
    @1
    wceq
    @33
    @1
    @0
    fndm
    syl
    syl5sseqr
    jca
    @27
    @9
    wfun
    #
    @30
    @9
    cdm
    #
    wss
    @27
    @11
    @41
    @35
    @10
    @9
    fnfun
    syl
    #
    @27
    @10
    @30
    @42
    @1
    @10
    inss2
    #
    @27
    @11
    @42
    @10
    wceq
    @35
    @10
    @9
    fndm
    syl
    syl5sseqr
    jca
    @30
    @1
    wss
    @27
    @6
    @5
    va
    @30
    wral
    @40
    @2
    @6
    @15
    @26
    @22
    simp2lr
    @5
    va
    @30
    @1
    ssralv
    mpsyl
    @30
    @10
    wss
    @27
    @14
    @13
    va
    @30
    wral
    @44
    @11
    @14
    @7
    @26
    @22
    simp2rr
    @13
    va
    @30
    @10
    ssralv
    mpsyl
    tfrlem1
    @31
    @32
    va
    @17
    @30
    @3
    @17
    wceq
    @4
    @28
    @12
    @29
    @3
    @17
    @0
    fveq2
    @3
    @17
    @9
    fveq2
    eqeq12d
    rspcv
    sylc
    @27
    @37
    @19
    @28
    @18
    wceq
    @39
    @34
    @17
    @18
    @0
    funbrfv
    sylc
    @27
    @41
    @21
    @29
    @20
    wceq
    @43
    @36
    @17
    @20
    @9
    funbrfv
    sylc
    3eqtr3d
    3exp
    rexlimivv
    sylbir
    syl2anb
end
