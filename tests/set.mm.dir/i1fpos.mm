include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "ccnv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "simpr.mm"
include "biantrurd.mm"
include "i1ff.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "syl6bbr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "adantr.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "3bitr4d.mm"
include "ifbid.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "cvol.mm"
include "i1fima.mm"
include "eqid.mm"
include "i1fres.mm"
include "mpdan.mm"
include "eqeltrd.mm"

theorem i1fpos
  let vx: setvar x
  let cF: class F
  let cG: class G
  assume i1fpos.1: |- G = ( x e. RR |-> if ( 0 <_ ( F ` x ) , ( F ` x ) , 0 ) )

  disjoint F x
  assert |- ( F e. dom S.1 -> G e. dom S.1 )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    cG
    vx
    cr
    vx
    cv
    #
    cF
    ccnv
    cc0
    cpnf
    cico
    co
    #
    cima
    #
    wcel
    #
    @2
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    @0
    @1
    cG
    vx
    cr
    cc0
    @6
    cle
    wbr
    #
    @6
    cc0
    cif
    #
    cmpt
    @8
    i1fpos.1
    @1
    vx
    cr
    @10
    @7
    @1
    @2
    cr
    wcel
    #
    wa
    #
    @9
    @5
    @6
    cc0
    @12
    @6
    @3
    wcel
    #
    @11
    @13
    wa
    #
    @9
    @5
    @12
    @11
    @13
    @1
    @11
    simpr
    biantrurd
    @12
    @9
    @6
    cr
    wcel
    #
    @9
    wa
    @13
    @12
    @15
    @9
    @1
    cr
    cr
    @2
    cF
    cF
    i1ff
    #
    ffvelrnda
    biantrurd
    @6
    elrege0
    syl6bbr
    @12
    cr
    cr
    cF
    wf
    #
    cF
    cr
    wfn
    @5
    @14
    wb
    @1
    @17
    @11
    @16
    adantr
    cr
    cr
    cF
    ffn
    cr
    @2
    @3
    cF
    elpreima
    3syl
    3bitr4d
    ifbid
    mpteq2dva
    syl5eq
    @1
    @4
    cvol
    cdm
    wcel
    @8
    @0
    wcel
    @3
    cF
    i1fima
    vx
    @4
    cF
    @8
    @8
    eqid
    i1fres
    mpdan
    eqeltrd
end
