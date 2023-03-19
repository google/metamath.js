include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ccom.mm"
include "id.mm"
include "idltrn.mm"
include "eqid.mm"
include "dvavadd.mm"
include "syl12anc.mm"
include "wf1o.mm"
include "wf.mm"
include "f1oi.mm"
include "f1of.mm"
include "fcoi2.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "clmod.mm"
include "cbs.mm"
include "wb.mm"
include "clvec.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "dvavbase.mm"
include "eleqtrrd.mm"
include "lmod0vid.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem dva0g
  let cB: class B
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume dva0g.b: |- B = ( Base ` K )
  assume dva0g.h: |- H = ( LHyp ` K )
  assume dva0g.t: |- T = ( ( LTrn ` K ) ` W )
  assume dva0g.u: |- U = ( ( DVecA ` K ) ` W )
  assume dva0g.z: |- .0. = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> .0. = ( _I |` B ) )

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
    @1
    cU
    cplusg
    cfv
    #
    co
    #
    @1
    wceq
    #
    c.0
    @1
    wceq
    #
    @0
    @3
    @1
    @1
    ccom
    #
    @1
    @0
    @0
    @1
    cT
    wcel
    #
    @7
    @3
    @6
    wceq
    @0
    id
    cB
    cT
    cH
    cK
    cW
    dva0g.b
    dva0g.h
    dva0g.t
    idltrn
    #
    @8
    @2
    cT
    cU
    @1
    @1
    cH
    cK
    chlt
    cW
    dva0g.h
    dva0g.t
    dva0g.u
    @2
    eqid
    #
    dvavadd
    syl12anc
    cB
    cB
    @1
    wf1o
    cB
    cB
    @1
    wf
    @6
    @1
    wceq
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
    syl6eq
    @0
    cU
    clmod
    wcel
    #
    @1
    cU
    cbs
    cfv
    #
    wcel
    @4
    @5
    wb
    @0
    cU
    clvec
    wcel
    @10
    cU
    cH
    cK
    cW
    dva0g.h
    dva0g.u
    dvalvec
    cU
    lveclmod
    syl
    @0
    @1
    cT
    @11
    @8
    cT
    cU
    cH
    cK
    @11
    cW
    chlt
    dva0g.h
    dva0g.t
    dva0g.u
    @11
    eqid
    #
    dvavbase
    eleqtrrd
    @2
    @11
    cU
    @1
    c.0
    @12
    @9
    dva0g.z
    lmod0vid
    syl2anc
    mpbid
end
