include "cnrm.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "cuni.mm"
include "cdif.mm"
include "wrex.mm"
include "simpl.mm"
include "simpr2.mm"
include "eqid.mm"
include "cldopn.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "wb.mm"
include "cldss.mm"
include "reldisj.mm"
include "3syl.mm"
include "mpbid.mm"
include "nrmsep3.mm"
include "syl13anc.mm"
include "ssdifin0.mm"
include "anim2i.mm"
include "reximi.mm"

theorem nrmsep2
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint C x
  disjoint D x
  disjoint J x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C y
  disjoint D y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint J f
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g o
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint J g
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint J m
  disjoint n o
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint J o
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( ( J e. Nrm /\ ( C e. ( Clsd ` J ) /\ D e. ( Clsd ` J ) /\ ( C i^i D ) = (/) ) ) -> E. x e. J ( C C_ x /\ ( ( ( cls ` J ) ` x ) i^i D ) = (/) ) )

  proof
    cJ
    cnrm
    wcel
    #
    cC
    cJ
    ccld
    cfv
    #
    wcel
    #
    cD
    @1
    wcel
    #
    cC
    cD
    cin
    c0
    wceq
    #
    w3a
    #
    wa
    #
    cC
    vx
    cv
    #
    wss
    #
    @7
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    cuni
    #
    cD
    cdif
    #
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @8
    @9
    cD
    cin
    c0
    wceq
    #
    wa
    #
    vx
    cJ
    wrex
    @6
    @0
    @11
    cJ
    wcel
    #
    @2
    cC
    @11
    wss
    #
    @14
    @0
    @5
    simpl
    @6
    @3
    @17
    @0
    @2
    @3
    @4
    simpr2
    cD
    cJ
    @10
    @10
    eqid
    #
    cldopn
    syl
    @0
    @2
    @3
    @4
    simpr1
    #
    @6
    @4
    @18
    @0
    @2
    @3
    @4
    simpr3
    @6
    @2
    cC
    @10
    wss
    @4
    @18
    wb
    @20
    cC
    cJ
    @10
    @19
    cldss
    cC
    cD
    @10
    reldisj
    3syl
    mpbid
    vx
    @11
    cC
    cJ
    nrmsep3
    syl13anc
    @13
    @16
    vx
    cJ
    @12
    @15
    @8
    @9
    @10
    cD
    ssdifin0
    anim2i
    reximi
    syl
end
