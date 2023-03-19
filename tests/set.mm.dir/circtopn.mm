include "cqtop.mm"
include "co.mm"
include "cpw.mm"
include "wss.mm"
include "crefld.mm"
include "cimas.mm"
include "ctopn.mm"
include "cfv.mm"
include "wceq.mm"
include "cuni.mm"
include "pwuni.mm"
include "ctop.mm"
include "wcel.mm"
include "cr.mm"
include "wfo.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "efifo.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "qtopuni.mm"
include "mp2an.mm"
include "pweqi.mm"
include "sseqtr4i.mm"
include "cbs.mm"
include "wtru.mm"
include "ccms.mm"
include "eqidd.mm"
include "rebase.mm"
include "a1i.mm"
include "recms.mm"
include "imasbas.mm"
include "trud.mm"
include "cts.mm"
include "retopn.mm"
include "eqtri.mm"
include "eqid.mm"
include "imastset.mm"
include "eqcomi.mm"
include "topnid.mm"
include "ax-mp.mm"

theorem circtopn
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
  assert |- ( J qTop F ) = ( TopOpen ` ( F "s RRfld ) )

  proof
    cJ
    cF
    cqtop
    co
    #
    cC
    cpw
    #
    wss
    @0
    cF
    crefld
    cimas
    co
    #
    ctopn
    cfv
    wceq
    @0
    @0
    cuni
    #
    cpw
    @1
    @0
    pwuni
    cC
    @3
    cJ
    ctop
    wcel
    cr
    cC
    cF
    wfo
    #
    cC
    @3
    wceq
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    circtopn.j
    retop
    eqeltri
    vx
    cC
    cF
    circtopn.f
    circtopn.c
    efifo
    #
    cF
    cJ
    cr
    cC
    cr
    @5
    cuni
    cJ
    cuni
    uniretop
    cJ
    @5
    circtopn.j
    unieqi
    eqtr4i
    qtopuni
    mp2an
    pweqi
    sseqtr4i
    cC
    @0
    @2
    cC
    @2
    cbs
    cfv
    wceq
    wtru
    cC
    crefld
    @2
    cF
    cr
    ccms
    wtru
    @2
    eqidd
    #
    cr
    crefld
    cbs
    cfv
    wceq
    wtru
    rebase
    a1i
    #
    @4
    wtru
    @6
    a1i
    #
    crefld
    ccms
    wcel
    wtru
    recms
    a1i
    #
    imasbas
    trud
    @2
    cts
    cfv
    #
    @0
    @11
    @0
    wceq
    wtru
    cC
    crefld
    @2
    cF
    cJ
    @11
    cr
    ccms
    @7
    @8
    @9
    @10
    cJ
    @5
    crefld
    ctopn
    cfv
    circtopn.j
    retopn
    eqtri
    @11
    eqid
    imastset
    trud
    eqcomi
    topnid
    ax-mp
end
