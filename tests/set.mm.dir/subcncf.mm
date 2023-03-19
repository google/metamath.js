include "cmin.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "subcn.mm"
include "a1i.mm"
include "cncfmpt2f.mm"

theorem subcncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X
  let vk: setvar k
  assume subcncf.a: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> CC ) )
  assume subcncf.b: |- ( ph -> ( x e. X |-> B ) e. ( X -cn-> CC ) )

  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( x e. X |-> ( A - B ) ) e. ( X -cn-> CC ) )

  proof
    wph
    vx
    cA
    cB
    cmin
    ccnfld
    ctopn
    cfv
    #
    cX
    @0
    eqid
    #
    cmin
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
    subcn
    a1i
    subcncf.a
    subcncf.b
    cncfmpt2f
end
