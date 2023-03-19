include "cn.mm"
include "cr.mm"
include "cv.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cdiv.mm"
include "cmpt2.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cc0.mm"
include "cmpt.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmpt2v.mm"
include "eleq1.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "negeq.mm"
include "id.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "mbfi1fseqlem6.mm"

theorem mbfi1fseq
  let wph: wff ph
  let vx: setvar x
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cJ: class J
  let cA: class A
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )

  disjoint g n
  disjoint g x
  disjoint F g
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint n ph
  disjoint ph x
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g y
  disjoint g z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G x
  disjoint J m
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint A m
  disjoint A x
  disjoint A y
  assert |- ( ph -> E. g ( g : NN --> dom S.1 /\ A. n e. NN ( 0p oR <_ ( g ` n ) /\ ( g ` n ) oR <_ ( g ` ( n + 1 ) ) ) /\ A. x e. RR ( n e. NN |-> ( ( g ` n ) ` x ) ) ~~> ( F ` x ) ) )

  proof
    wph
    vx
    vy
    vg
    vk
    vn
    cF
    vm
    cn
    vy
    cr
    vy
    cv
    #
    vm
    cv
    #
    cneg
    #
    @1
    cicc
    co
    #
    wcel
    #
    @1
    @0
    vj
    vz
    cn
    cr
    vz
    cv
    #
    cF
    cfv
    #
    c2
    vj
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @8
    cdiv
    co
    #
    cmpt2
    #
    co
    #
    @1
    cle
    wbr
    #
    @13
    @1
    cif
    #
    cc0
    cif
    #
    cmpt
    #
    cmpt
    @12
    mbfi1fseq.1
    mbfi1fseq.2
    vj
    vz
    vk
    vy
    cn
    cr
    @11
    @0
    cF
    cfv
    #
    c2
    vk
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @20
    cdiv
    co
    @6
    @20
    cmul
    co
    #
    cfl
    cfv
    #
    @20
    cdiv
    co
    vj
    vk
    weq
    #
    @10
    @24
    @8
    @20
    cdiv
    @25
    @9
    @23
    cfl
    @25
    @8
    @20
    @6
    cmul
    @7
    @19
    c2
    cexp
    oveq2
    #
    oveq2d
    fveq2d
    @26
    oveq12d
    vz
    vy
    weq
    #
    @24
    @22
    @20
    cdiv
    @27
    @23
    @21
    cfl
    @27
    @6
    @18
    @20
    cmul
    @5
    @0
    cF
    fveq2
    oveq1d
    fveq2d
    oveq1d
    cbvmpt2v
    vm
    vk
    cn
    @17
    vx
    cr
    vx
    cv
    #
    @19
    cneg
    #
    @19
    cicc
    co
    #
    wcel
    #
    @19
    @28
    @12
    co
    #
    @19
    cle
    wbr
    #
    @32
    @19
    cif
    #
    cc0
    cif
    #
    cmpt
    #
    vm
    vk
    weq
    #
    @17
    vx
    cr
    @28
    @3
    wcel
    #
    @1
    @28
    @12
    co
    #
    @1
    cle
    wbr
    #
    @39
    @1
    cif
    #
    cc0
    cif
    #
    cmpt
    @36
    vy
    vx
    cr
    @16
    @42
    vy
    vx
    weq
    #
    @4
    @38
    @15
    @41
    cc0
    @0
    @28
    @3
    eleq1
    @43
    @14
    @40
    @13
    @39
    @1
    @43
    @13
    @39
    @1
    cle
    @0
    @28
    @1
    @12
    oveq2
    #
    breq1d
    @44
    ifbieq1d
    ifbieq1d
    cbvmptv
    @37
    vx
    cr
    @42
    @35
    @37
    @38
    @31
    @41
    @34
    cc0
    @37
    @3
    @30
    @28
    @37
    @2
    @29
    @1
    @19
    cicc
    @1
    @19
    negeq
    @37
    id
    #
    oveq12d
    eleq2d
    @37
    @40
    @33
    @39
    @1
    @32
    @19
    @37
    @39
    @32
    @1
    @19
    cle
    @1
    @19
    @28
    @12
    oveq1
    #
    @45
    breq12d
    @46
    @45
    ifbieq12d
    ifbieq1d
    mpteq2dv
    syl5eq
    cbvmptv
    mbfi1fseqlem6
end
