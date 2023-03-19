include "cr.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfn.mm"
include "cqtop.mm"
include "co.mm"
include "ccn.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "wfo.mm"
include "efifo.mm"
include "fofn.mm"
include "ax-mp.mm"
include "qtopid.mm"
include "mp2an.mm"

theorem circcn
  let vx: setvar x
  let cC: class C
  let cF: class F
  let cI: class I
  let cJ: class J
  assume circtopn.i: |- I = ( 0 [,] ( 2 x. _pi ) )
  assume circtopn.j: |- J = ( topGen ` ran (,) )
  assume circtopn.f: |- F = ( x e. RR |-> ( exp ` ( _i x. x ) ) )
  assume circtopn.c: |- C = ( `' abs " { 1 } )

  disjoint C x
  assert |- F e. ( J Cn ( J qTop F ) )

  proof
    cJ
    cr
    ctopon
    cfv
    #
    wcel
    cF
    cr
    wfn
    #
    cF
    cJ
    cJ
    cF
    cqtop
    co
    ccn
    co
    wcel
    cJ
    cioo
    crn
    ctg
    cfv
    @0
    circtopn.j
    retopon
    eqeltri
    cr
    cC
    cF
    wfo
    @1
    vx
    cC
    cF
    circtopn.f
    circtopn.c
    efifo
    cr
    cC
    cF
    fofn
    ax-mp
    cF
    cJ
    cr
    qtopid
    mp2an
end
