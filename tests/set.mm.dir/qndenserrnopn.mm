include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "cq.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "crrx.mm"
include "cfv.mm"
include "cds.mm"
include "cfn.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "qndenserrnopnlem.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem qndenserrnopn
  let wph: wff ph
  let vy: setvar y
  let cI: class I
  let cJ: class J
  let cV: class V
  let vx: setvar x
  let vk: setvar k
  assume qndenserrnopn.i: |- ( ph -> I e. Fin )
  assume qndenserrnopn.j: |- J = ( TopOpen ` ( RR^ ` I ) )
  assume qndenserrnopn.v: |- ( ph -> V e. J )
  assume qndenserrnopn.n: |- ( ph -> V =/= (/) )

  disjoint I y
  disjoint V y
  disjoint ph y
  disjoint I x
  disjoint x y
  disjoint V x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. y e. ( QQ ^m I ) y e. V )

  proof
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vx
    wex
    #
    vy
    cv
    cV
    wcel
    vy
    cq
    cI
    cmap
    co
    wrex
    #
    wph
    cV
    c0
    wne
    @2
    qndenserrnopn.n
    vx
    cV
    n0
    sylib
    wph
    @1
    @3
    vx
    wph
    @1
    @3
    wph
    @1
    wa
    vy
    cI
    crrx
    cfv
    cds
    cfv
    #
    cI
    cJ
    cV
    @0
    wph
    cI
    cfn
    wcel
    @1
    qndenserrnopn.i
    adantr
    qndenserrnopn.j
    wph
    cV
    cJ
    wcel
    @1
    qndenserrnopn.v
    adantr
    wph
    @1
    simpr
    @4
    eqid
    qndenserrnopnlem
    ex
    exlimdv
    mpd
end
