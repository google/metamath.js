include "cr.mm"
include "ccnfld.mm"
include "csra.mm"
include "cfv.mm"
include "cnx.mm"
include "cip.mm"
include "cc.mm"
include "cv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "ndxid.mm"
include "wne.mm"
include "c8.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "5lt8.mm"
include "nnrei.mm"
include "5re.mm"
include "8re.mm"
include "lttri.mm"
include "mpan2.mm"
include "ltnei.mm"
include "syl.mm"
include "necomd.mm"
include "jaoi.mm"
include "ax-mp.mm"
include "ndxarg.mm"
include "ipndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "wceq.mm"
include "wtru.mm"
include "eqidd.mm"
include "cbs.mm"
include "wss.mm"
include "ax-resscn.mm"
include "cnfldbas.mm"
include "sseqtri.mm"
include "a1i.mm"
include "sralem.mm"
include "trud.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem cchhllem
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cE: class E
  let cN: class N
  assume cchhl.c: |- C = ( ( ( subringAlg ` CCfld ) ` RR ) sSet <. ( .i ` ndx ) , ( x e. CC , y e. CC |-> ( x x. ( * ` y ) ) ) >. )
  assume cchhllem.2: |- E = Slot N
  assume cchhllem.3: |- N e. NN
  assume cchhllem.4: |- ( N < 5 \/ 8 < N )

  disjoint x y
  assert |- ( E ` CCfld ) = ( E ` C )

  proof
    cr
    ccnfld
    csra
    cfv
    cfv
    #
    cE
    cfv
    #
    @0
    cnx
    cip
    cfv
    #
    vx
    vy
    cc
    cc
    vx
    cv
    vy
    cv
    ccj
    cfv
    cmul
    co
    cmpt2
    #
    cop
    csts
    co
    #
    cE
    cfv
    ccnfld
    cE
    cfv
    #
    cC
    cE
    cfv
    @3
    @2
    cE
    @0
    cE
    cN
    cchhllem.2
    cchhllem.3
    ndxid
    cnx
    cE
    cfv
    #
    @2
    wne
    cN
    c8
    wne
    #
    cN
    c5
    clt
    wbr
    #
    c8
    cN
    clt
    wbr
    #
    wo
    @7
    cchhllem.4
    @8
    @7
    @9
    @8
    c8
    cN
    @8
    cN
    c8
    clt
    wbr
    #
    c8
    cN
    wne
    @8
    c5
    c8
    clt
    wbr
    @10
    5lt8
    cN
    c5
    c8
    cN
    cchhllem.3
    nnrei
    #
    5re
    8re
    lttri
    mpan2
    cN
    c8
    @11
    8re
    ltnei
    syl
    necomd
    c8
    cN
    8re
    @11
    ltnei
    jaoi
    ax-mp
    @6
    cN
    @2
    c8
    cE
    cN
    cchhllem.2
    cchhllem.3
    ndxarg
    ipndx
    neeq12i
    mpbir
    setsnid
    @5
    @1
    wceq
    wtru
    @0
    cr
    cE
    cN
    ccnfld
    wtru
    @0
    eqidd
    cr
    ccnfld
    cbs
    cfv
    #
    wss
    wtru
    cr
    cc
    @12
    ax-resscn
    cnfldbas
    sseqtri
    a1i
    cchhllem.2
    cchhllem.3
    cchhllem.4
    sralem
    trud
    cC
    @4
    cE
    cchhl.c
    fveq2i
    3eqtr4i
end
