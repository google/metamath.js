include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wf1.mm"
include "cab.mm"
include "chash.mm"
include "cfv.mm"
include "cfa.mm"
include "cbc.mm"
include "co.mm"
include "cmul.mm"
include "wf1o.mm"
include "wceq.mm"
include "hashf1.mm"
include "anidms.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "enrefg.mm"
include "f1finf1o.mm"
include "mpancom.mm"
include "abbidv.mm"
include "fveq2d.mm"
include "c1.mm"
include "cn0.mm"
include "hashcl.mm"
include "bcnn.mm"
include "syl.mm"
include "oveq2d.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem hashfac
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A f
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A e. Fin -> ( # ` { f | f : A -1-1-onto-> A } ) = ( ! ` ( # ` A ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cA
    vf
    cv
    #
    wf1
    #
    vf
    cab
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cfa
    cfv
    #
    @5
    @5
    cbc
    co
    #
    cmul
    co
    #
    cA
    cA
    @1
    wf1o
    #
    vf
    cab
    #
    chash
    cfv
    @6
    @0
    @4
    @8
    wceq
    cA
    cA
    vf
    hashf1
    anidms
    @0
    @3
    @10
    chash
    @0
    @2
    @9
    vf
    cA
    cA
    cen
    wbr
    @0
    @2
    @9
    wb
    cA
    cfn
    enrefg
    cA
    cA
    @1
    f1finf1o
    mpancom
    abbidv
    fveq2d
    @0
    @8
    @6
    c1
    cmul
    co
    @6
    @0
    @7
    c1
    @6
    cmul
    @0
    @5
    cn0
    wcel
    #
    @7
    c1
    wceq
    cA
    hashcl
    #
    @5
    bcnn
    syl
    oveq2d
    @0
    @6
    @0
    @6
    @0
    @11
    @6
    cn
    wcel
    @12
    @5
    faccl
    syl
    nncnd
    mulid1d
    eqtrd
    3eqtr3d
end
