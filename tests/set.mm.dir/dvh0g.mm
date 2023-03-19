include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ccom.mm"
include "csca.mm"
include "ctendo.mm"
include "id.mm"
include "idltrn.mm"
include "eqid.mm"
include "tendo0cl.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fcoi2.mm"
include "mp2b.mm"
include "a1i.mm"
include "cv.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "dvhfplusr.mm"
include "oveqd.mm"
include "tendo0pl.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "opeq12d.mm"
include "clmod.mm"
include "cbs.mm"
include "wb.mm"
include "dvhlmod.mm"
include "dvhelvbasei.mm"
include "syl12anc.mm"
include "lmod0vid.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem dvh0g
  let cB: class B
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vt: setvar t
  assume dvh0g.b: |- B = ( Base ` K )
  assume dvh0g.h: |- H = ( LHyp ` K )
  assume dvh0g.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvh0g.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh0g.z: |- .0. = ( 0g ` U )
  assume dvh0g.o: |- O = ( f e. T |-> ( _I |` B ) )

  disjoint B f
  disjoint H f
  disjoint K f
  disjoint T f
  disjoint W f
  disjoint f s
  disjoint f t
  disjoint s t
  disjoint K s
  disjoint K t
  disjoint T s
  disjoint T t
  disjoint W s
  disjoint W t
  assert |- ( ( K e. HL /\ W e. H ) -> .0. = <. ( _I |` B ) , O >. )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cid
    cB
    cres
    #
    cO
    cop
    #
    @2
    cU
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    c.0
    @2
    wceq
    #
    @0
    @4
    @1
    @1
    ccom
    #
    cO
    cO
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    @2
    @0
    @0
    @1
    cT
    wcel
    #
    cO
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @12
    @14
    @4
    @11
    wceq
    @0
    id
    #
    cB
    cT
    cH
    cK
    cW
    dvh0g.b
    dvh0g.h
    dvh0g.t
    idltrn
    #
    cB
    cT
    vf
    @13
    cH
    cK
    cO
    cW
    dvh0g.b
    dvh0g.h
    dvh0g.t
    @13
    eqid
    #
    dvh0g.o
    tendo0cl
    #
    @16
    @18
    @8
    @3
    @9
    cO
    cO
    cT
    cU
    @13
    @1
    @1
    cH
    cK
    cW
    dvh0g.h
    dvh0g.t
    @17
    dvh0g.u
    @8
    eqid
    #
    @3
    eqid
    #
    @9
    eqid
    #
    dvhopvadd
    syl122anc
    @0
    @7
    @1
    @10
    cO
    @7
    @1
    wceq
    #
    @0
    cB
    cB
    @1
    wf1o
    cB
    cB
    @1
    wf
    @22
    cB
    f1oi
    cB
    cB
    @1
    f1of
    cB
    cB
    @1
    fcoi2
    mp2b
    a1i
    @0
    @10
    cO
    cO
    vs
    vt
    @13
    @13
    vf
    cT
    vf
    cv
    #
    vs
    cv
    cfv
    @23
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    cO
    @0
    @9
    @24
    cO
    cO
    vt
    @24
    @9
    cT
    cU
    vf
    @13
    @8
    cH
    cK
    chlt
    cW
    vs
    dvh0g.h
    dvh0g.t
    @17
    dvh0g.u
    @19
    @24
    eqid
    #
    @21
    dvhfplusr
    oveqd
    @0
    @14
    @25
    cO
    wceq
    @18
    vt
    cB
    @24
    cO
    cT
    vf
    @13
    cH
    cK
    cO
    cW
    vs
    dvh0g.b
    dvh0g.h
    dvh0g.t
    @17
    dvh0g.o
    @26
    tendo0pl
    mpdan
    eqtrd
    opeq12d
    eqtrd
    @0
    cU
    clmod
    wcel
    @2
    cU
    cbs
    cfv
    #
    wcel
    #
    @5
    @6
    wb
    @0
    cU
    cH
    cK
    cW
    dvh0g.h
    dvh0g.u
    @15
    dvhlmod
    @0
    @0
    @12
    @14
    @28
    @15
    @16
    @18
    cO
    cT
    cU
    @13
    @1
    cH
    cK
    @27
    cW
    chlt
    dvh0g.h
    dvh0g.t
    @17
    dvh0g.u
    @27
    eqid
    #
    dvhelvbasei
    syl12anc
    @3
    @27
    cU
    @2
    c.0
    @29
    @20
    dvh0g.z
    lmod0vid
    syl2anc
    mpbid
end
