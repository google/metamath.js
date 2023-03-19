include "ccmp.mm"
include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "wceq.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ctop.mm"
include "cmptop.mm"
include "fitop.mm"
include "fveq2d.mm"
include "tgtop.mm"
include "eqtr2d.mm"
include "syl.mm"
include "wss.mm"
include "selpw.mm"
include "cmpcov.mm"
include "3exp.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mp2and.mm"

theorem alexsubALTlem1
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume alexsubALT.1: |- X = U. J

  disjoint c d
  disjoint c x
  disjoint J c
  disjoint d x
  disjoint J d
  disjoint J x
  disjoint X c
  disjoint X d
  disjoint X x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d m
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( J e. Comp -> E. x ( J = ( topGen ` ( fi ` x ) ) /\ A. c e. ~P x ( X = U. c -> E. d e. ( ~P c i^i Fin ) X = U. d ) ) )

  proof
    cJ
    ccmp
    wcel
    #
    cJ
    cJ
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    #
    cX
    vc
    cv
    #
    cuni
    wceq
    #
    cX
    vd
    cv
    cuni
    wceq
    vd
    @4
    cpw
    cfn
    cin
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    #
    cJ
    vx
    cv
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    #
    @7
    vc
    @10
    cpw
    #
    wral
    #
    wa
    #
    vx
    wex
    @0
    cJ
    ctop
    wcel
    #
    @3
    cJ
    cmptop
    @17
    @2
    cJ
    ctg
    cfv
    cJ
    @17
    @1
    cJ
    ctg
    cJ
    fitop
    fveq2d
    cJ
    tgtop
    eqtr2d
    syl
    @0
    @7
    vc
    @8
    @4
    @8
    wcel
    @4
    cJ
    wss
    #
    @0
    @7
    vc
    cJ
    selpw
    @0
    @18
    @5
    @6
    @4
    cJ
    cX
    vd
    alexsubALT.1
    cmpcov
    3exp
    syl5bi
    ralrimiv
    @16
    @3
    @9
    wa
    vx
    cJ
    ccmp
    @10
    cJ
    wceq
    #
    @13
    @3
    @15
    @9
    @19
    @12
    @2
    cJ
    @19
    @11
    @1
    ctg
    @10
    cJ
    cfi
    fveq2
    fveq2d
    eqeq2d
    @19
    @7
    vc
    @14
    @8
    @10
    cJ
    pweq
    raleqdv
    anbi12d
    spcegv
    mp2and
end
