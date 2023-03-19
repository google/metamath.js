include "cmul.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "mulcn.mm"
include "a1i.mm"
include "cncfmpt2f.mm"

theorem mulcncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X
  assume mulcncf.1: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> CC ) )
  assume mulcncf.2: |- ( ph -> ( x e. X |-> B ) e. ( X -cn-> CC ) )

  disjoint X x
  disjoint ph x
  assert |- ( ph -> ( x e. X |-> ( A x. B ) ) e. ( X -cn-> CC ) )

  proof
    wph
    vx
    cA
    cB
    cmul
    ccnfld
    ctopn
    cfv
    #
    cX
    @0
    eqid
    #
    cmul
    @0
    @0
    ctx
    co
    @0
    ccn
    co
    wcel
    wph
    @0
    @1
    mulcn
    a1i
    mulcncf.1
    mulcncf.2
    cncfmpt2f
end
