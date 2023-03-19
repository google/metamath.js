include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmpt.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "iccvonmbllem.mm"

theorem iccvonmbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume iccvonmbl.x: |- ( ph -> X e. Fin )
  assume iccvonmbl.s: |- S = dom ( voln ` X )
  assume iccvonmbl.a: |- ( ph -> A : X --> RR )
  assume iccvonmbl.b: |- ( ph -> B : X --> RR )

  disjoint A i
  disjoint B i
  disjoint X i
  disjoint i ph
  disjoint A j
  disjoint A n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint B j
  disjoint B n
  disjoint S n
  disjoint X j
  disjoint X n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) [,] ( B ` i ) ) e. S )

  proof
    wph
    cA
    cB
    vn
    cn
    vj
    cX
    vj
    cv
    #
    cA
    cfv
    #
    c1
    vn
    cv
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    #
    cmpt
    vn
    cn
    vj
    cX
    @0
    cB
    cfv
    #
    @2
    caddc
    co
    #
    cmpt
    #
    cmpt
    cS
    vi
    vn
    cX
    iccvonmbl.x
    iccvonmbl.s
    iccvonmbl.a
    iccvonmbl.b
    vn
    cn
    @4
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @2
    cmin
    co
    #
    cmpt
    vj
    vi
    cX
    @3
    @10
    @0
    @8
    wceq
    #
    @1
    @9
    @2
    cmin
    @0
    @8
    cA
    fveq2
    oveq1d
    cbvmptv
    mpteq2i
    vn
    cn
    @7
    vi
    cX
    @8
    cB
    cfv
    #
    @2
    caddc
    co
    #
    cmpt
    vj
    vi
    cX
    @6
    @13
    @11
    @5
    @12
    @2
    caddc
    @0
    @8
    cB
    fveq2
    oveq1d
    cbvmptv
    mpteq2i
    iccvonmbllem
end
