include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cmap.mm"
include "cixp.mm"
include "wcel.mm"
include "ccid.mm"
include "wceq.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "cfunc.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "ccat.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "isfunc.mm"
include "mpbid.mm"
include "simp2d.mm"

theorem funcixp
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume funcixp.b: |- B = ( Base ` D )
  assume funcixp.h: |- H = ( Hom ` D )
  assume funcixp.j: |- J = ( Hom ` E )
  assume funcixp.f: |- ( ph -> F ( D Func E ) G )

  disjoint B z
  disjoint D z
  disjoint E z
  disjoint ph z
  disjoint F z
  disjoint G z
  disjoint J z
  disjoint H z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint E y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint X z
  disjoint Y z
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  assert |- ( ph -> G e. X_ z e. ( B X. B ) ( ( ( F ` ( 1st ` z ) ) J ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) ) )

  proof
    wph
    cB
    cE
    cbs
    cfv
    #
    cF
    wf
    #
    cG
    vz
    cB
    cB
    cxp
    vz
    cv
    #
    c1st
    cfv
    cF
    cfv
    @2
    c2nd
    cfv
    cF
    cfv
    cJ
    co
    @2
    cH
    cfv
    cmap
    co
    cixp
    wcel
    #
    vx
    cv
    #
    cD
    ccid
    cfv
    #
    cfv
    @4
    @4
    cG
    co
    cfv
    @4
    cF
    cfv
    #
    cE
    ccid
    cfv
    #
    cfv
    wceq
    vn
    cv
    #
    vm
    cv
    #
    @4
    vy
    cv
    #
    cop
    @2
    cD
    cco
    cfv
    #
    co
    co
    @4
    @2
    cG
    co
    cfv
    @8
    @10
    @2
    cG
    co
    cfv
    @9
    @4
    @10
    cG
    co
    cfv
    @6
    @10
    cF
    cfv
    cop
    @2
    cF
    cfv
    cE
    cco
    cfv
    #
    co
    co
    wceq
    vn
    @10
    @2
    cH
    co
    wral
    vm
    @4
    @10
    cH
    co
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    wa
    vx
    cB
    wral
    #
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    #
    wbr
    #
    @1
    @3
    @13
    w3a
    funcixp.f
    wph
    vx
    vy
    vz
    cB
    @0
    cD
    @11
    @5
    vm
    vn
    cE
    cF
    cG
    cH
    @7
    cJ
    @12
    funcixp.b
    @0
    eqid
    funcixp.h
    funcixp.j
    @5
    eqid
    @7
    eqid
    @11
    eqid
    @12
    eqid
    wph
    cD
    ccat
    wcel
    #
    cE
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    @14
    wcel
    #
    @16
    @17
    wa
    wph
    @15
    @19
    funcixp.f
    cF
    cG
    @14
    df-br
    sylib
    cD
    cE
    @18
    funcrcl
    syl
    #
    simpld
    wph
    @16
    @17
    @20
    simprd
    isfunc
    mpbid
    simp2d
end
