include "cn.mm"
include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "ovnsubadd2lem.mm"

theorem ovnsubadd2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume ovnsubadd2.x: |- ( ph -> X e. Fin )
  assume ovnsubadd2.a: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnsubadd2.b: |- ( ph -> B C_ ( RR ^m X ) )


  assert |- ( ph -> ( ( voln* ` X ) ` ( A u. B ) ) <_ ( ( ( voln* ` X ) ` A ) +e ( ( voln* ` X ) ` B ) ) )

  proof
    wph
    cA
    cB
    vm
    cn
    vm
    cv
    #
    c1
    wceq
    #
    cA
    @0
    c2
    wceq
    #
    cB
    c0
    cif
    #
    cif
    #
    cmpt
    vn
    cX
    ovnsubadd2.x
    ovnsubadd2.a
    ovnsubadd2.b
    vm
    vn
    cn
    @4
    vn
    cv
    #
    c1
    wceq
    #
    cA
    @5
    c2
    wceq
    #
    cB
    c0
    cif
    #
    cif
    @0
    @5
    wceq
    #
    @1
    @6
    @3
    @8
    cA
    @0
    @5
    c1
    eqeq1
    @9
    @2
    @7
    cB
    c0
    @0
    @5
    c2
    eqeq1
    ifbid
    ifbieq2d
    cbvmptv
    ovnsubadd2lem
end
