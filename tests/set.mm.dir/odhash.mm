include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cpnf.mm"
include "cz.mm"
include "chash.mm"
include "csn.mm"
include "cvv.mm"
include "cfn.mm"
include "wn.mm"
include "zex.mm"
include "com.mm"
include "ominf.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "cn.mm"
include "znnen.mm"
include "nnenom.mm"
include "entri.mm"
include "enfi.mm"
include "ax-mp.mm"
include "mtbir.mm"
include "hashinf.mm"
include "mp2an.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "wf1o.mm"
include "eqid.mm"
include "odf1o1.mm"
include "f1oen.mm"
include "hasheni.mm"
include "3syl.mm"
include "syl5reqr.mm"

theorem odhash
  let cA: class A
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume odhash.x: |- X = ( Base ` G )
  assume odhash.o: |- O = ( od ` G )
  assume odhash.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) = 0 ) -> ( # ` ( K ` { A } ) ) = +oo )

  proof
    cG
    cgrp
    wcel
    cA
    cX
    wcel
    cA
    cO
    cfv
    cc0
    wceq
    w3a
    #
    cpnf
    cz
    chash
    cfv
    #
    cA
    csn
    cK
    cfv
    #
    chash
    cfv
    #
    cz
    cvv
    wcel
    cz
    cfn
    wcel
    #
    wn
    @1
    cpnf
    wceq
    zex
    @4
    com
    cfn
    wcel
    #
    ominf
    cz
    com
    cen
    wbr
    @4
    @5
    wb
    cz
    cn
    com
    znnen
    nnenom
    entri
    cz
    com
    enfi
    ax-mp
    mtbir
    cz
    cvv
    hashinf
    mp2an
    @0
    cz
    @2
    vx
    cz
    vx
    cv
    cA
    cG
    cmg
    cfv
    #
    co
    cmpt
    #
    wf1o
    cz
    @2
    cen
    wbr
    @1
    @3
    wceq
    vx
    cA
    @6
    cG
    cK
    cO
    cX
    odhash.x
    @6
    eqid
    odhash.o
    odhash.k
    odf1o1
    cz
    @2
    @7
    zex
    f1oen
    cz
    @2
    hasheni
    3syl
    syl5reqr
end
