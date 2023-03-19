include "wcel.mm"
include "cgrp.mm"
include "wss.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wceq.mm"
include "w3a.mm"
include "csubg.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "symggrp.mm"
include "simp1.mm"
include "anim12i.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "symgplusg.mm"
include "eqcomi.mm"
include "reseq1i.mm"
include "resmpt2.mm"
include "anidms.mm"
include "syl5reqr.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "jca.mm"
include "adantl.mm"
include "grpissubg.mm"
include "sylc.mm"
include "ex.mm"

theorem pgrpsubgsymg
  let cA: class A
  let cB: class B
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  assume pgrpsubgsymgbi.g: |- G = ( SymGrp ` A )
  assume pgrpsubgsymgbi.b: |- B = ( Base ` G )
  assume pgrpsubgsymg.c: |- F = ( Base ` P )

  disjoint A f
  disjoint A g
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint F f
  disjoint F g
  assert |- ( A e. V -> ( ( P e. Grp /\ F C_ B /\ ( +g ` P ) = ( f e. F , g e. F |-> ( f o. g ) ) ) -> F e. ( SubGrp ` G ) ) )

  proof
    cA
    cV
    wcel
    #
    cP
    cgrp
    wcel
    #
    cF
    cB
    wss
    #
    cP
    cplusg
    cfv
    #
    vf
    vg
    cF
    cF
    vf
    cv
    vg
    cv
    ccom
    #
    cmpt2
    #
    wceq
    #
    w3a
    #
    cF
    cG
    csubg
    cfv
    wcel
    #
    @0
    @7
    wa
    cG
    cgrp
    wcel
    #
    @1
    wa
    @2
    @3
    cG
    cplusg
    cfv
    #
    cF
    cF
    cxp
    #
    cres
    #
    wceq
    #
    wa
    #
    @8
    @0
    @9
    @7
    @1
    cA
    cG
    cV
    pgrpsubgsymgbi.g
    symggrp
    @1
    @2
    @6
    simp1
    anim12i
    @7
    @14
    @0
    @7
    @2
    @13
    @1
    @2
    @6
    simp2
    @7
    @3
    @5
    @12
    @1
    @2
    @6
    simp3
    @2
    @1
    @5
    @12
    wceq
    @6
    @2
    @12
    vf
    vg
    cB
    cB
    @4
    cmpt2
    #
    @11
    cres
    #
    @5
    @15
    @10
    @11
    @10
    @15
    cA
    cB
    @10
    vf
    vg
    cG
    pgrpsubgsymgbi.g
    pgrpsubgsymgbi.b
    @10
    eqid
    symgplusg
    eqcomi
    reseq1i
    @2
    @16
    @5
    wceq
    vf
    vg
    cB
    cB
    cF
    cF
    @4
    resmpt2
    anidms
    syl5reqr
    3ad2ant2
    eqtrd
    jca
    adantl
    cB
    cF
    cG
    cP
    pgrpsubgsymgbi.b
    pgrpsubgsymg.c
    grpissubg
    sylc
    ex
end
