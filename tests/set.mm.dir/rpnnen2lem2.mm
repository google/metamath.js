include "cn.mm"
include "wss.mm"
include "cr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cn0.mm"
include "1re.mm"
include "3nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "sylancr.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "adantl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cpw.mm"
include "wceq.mm"
include "nnex.mm"
include "elpw2.mm"
include "eleq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylbir.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem rpnnen2lem2
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- ( A C_ NN -> ( F ` A ) : NN --> RR )

  proof
    cA
    cn
    wss
    #
    cn
    cr
    cA
    cF
    cfv
    #
    wf
    cn
    cr
    vn
    cn
    vn
    cv
    #
    cA
    wcel
    #
    c1
    c3
    cdiv
    co
    #
    @2
    cexp
    co
    #
    cc0
    cif
    #
    cmpt
    #
    wf
    @0
    vn
    cn
    @6
    cr
    @7
    @2
    cn
    wcel
    #
    @6
    cr
    wcel
    #
    @0
    @8
    @5
    cr
    wcel
    #
    cc0
    cr
    wcel
    @9
    @8
    @4
    cr
    wcel
    #
    @2
    cn0
    wcel
    @10
    c1
    cr
    wcel
    c3
    cn
    wcel
    @11
    1re
    3nn
    c1
    c3
    nndivre
    mp2an
    @2
    nnnn0
    @4
    @2
    reexpcl
    sylancr
    0re
    @3
    @5
    cc0
    cr
    ifcl
    sylancl
    adantl
    @7
    eqid
    fmptd
    @0
    cn
    cr
    @1
    @7
    @0
    cA
    cn
    cpw
    #
    wcel
    @1
    @7
    wceq
    cA
    cn
    nnex
    elpw2
    vx
    cA
    vn
    cn
    @2
    vx
    cv
    #
    wcel
    #
    @5
    cc0
    cif
    #
    cmpt
    @7
    @12
    cF
    @13
    cA
    wceq
    #
    vn
    cn
    @15
    @6
    @16
    @14
    @3
    @5
    cc0
    @13
    cA
    @2
    eleq2
    ifbid
    mpteq2dv
    rpnnen2.1
    vn
    cn
    @6
    nnex
    mptex
    fvmpt
    sylbir
    feq1d
    mpbird
end
