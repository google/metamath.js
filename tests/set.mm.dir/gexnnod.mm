include "cgrp.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "nnne0.mm"
include "3ad2ant2.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "0dvds.mm"
include "syl.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "gexod.mm"
include "3adant2.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "cn0.mm"
include "wo.mm"
include "odcl.mm"
include "3ad2ant3.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"

theorem gexnnod
  let cA: class A
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vx: setvar x
  let cN: class N
  assume gexod.1: |- X = ( Base ` G )
  assume gexod.2: |- E = ( gEx ` G )
  assume gexod.3: |- O = ( od ` G )


  assert |- ( ( G e. Grp /\ E e. NN /\ A e. X ) -> ( O ` A ) e. NN )

  proof
    cG
    cgrp
    wcel
    #
    cE
    cn
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @4
    cc0
    wceq
    #
    @3
    @6
    cc0
    cE
    cdvds
    wbr
    #
    @3
    @7
    wn
    cE
    cc0
    wne
    #
    @1
    @0
    @8
    @2
    cE
    nnne0
    3ad2ant2
    @3
    @7
    cE
    cc0
    @3
    cE
    cz
    wcel
    #
    @7
    cE
    cc0
    wceq
    wb
    @1
    @0
    @9
    @2
    cE
    nnz
    3ad2ant2
    cE
    0dvds
    syl
    necon3bbid
    mpbird
    @3
    @4
    cE
    cdvds
    wbr
    #
    @6
    @7
    @0
    @2
    @10
    @1
    cA
    cE
    cG
    cO
    cX
    gexod.1
    gexod.2
    gexod.3
    gexod
    3adant2
    @4
    cc0
    cE
    cdvds
    breq1
    syl5ibcom
    mtod
    @3
    @5
    @6
    @3
    @4
    cn0
    wcel
    #
    @5
    @6
    wo
    @2
    @0
    @11
    @1
    cA
    cG
    cO
    cX
    gexod.1
    gexod.3
    odcl
    3ad2ant3
    @4
    elnn0
    sylib
    ord
    mt3d
end
