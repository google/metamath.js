include "cid.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "chlt.mm"
include "wa.mm"
include "ctendo.mm"
include "cfv.mm"
include "idltrn.mm"
include "syl.mm"
include "eqid.mm"
include "tendoidcl.mm"
include "dvhelvbasei.mm"
include "syl12anc.mm"
include "cmpt.mm"
include "tendo1ne0.mm"
include "wceq.mm"
include "dvh0g.mm"
include "eqtr.mm"
include "wb.mm"
include "opthg.mm"
include "syl2anc.mm"
include "simpr.mm"
include "syl6bi.mm"
include "syl5.mm"
include "mpan2d.mm"
include "necon3d.mm"
include "mpd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"

theorem dvheveccl
  let wph: wff ph
  let cB: class B
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  assume dvheveccl.h: |- H = ( LHyp ` K )
  assume dvheveccl.b: |- B = ( Base ` K )
  assume dvheveccl.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvheveccl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvheveccl.v: |- V = ( Base ` U )
  assume dvheveccl.z: |- .0. = ( 0g ` U )
  assume dvheveccl.e: |- E = <. ( _I |` B ) , ( _I |` T ) >.
  assume dvheveccl.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> E e. ( V \ { .0. } ) )

  proof
    wph
    cE
    cid
    cB
    cres
    #
    cid
    cT
    cres
    #
    cop
    #
    cV
    c.0
    csn
    cdif
    #
    dvheveccl.e
    wph
    @2
    cV
    wcel
    #
    @2
    c.0
    wne
    #
    @2
    @3
    wcel
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    cT
    wcel
    #
    @1
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @4
    dvheveccl.k
    wph
    @6
    @7
    dvheveccl.k
    cB
    cT
    cH
    cK
    cW
    dvheveccl.b
    dvheveccl.h
    dvheveccl.t
    idltrn
    syl
    #
    wph
    @6
    @9
    dvheveccl.k
    cT
    @8
    cH
    cK
    cW
    dvheveccl.h
    dvheveccl.t
    @8
    eqid
    #
    tendoidcl
    syl
    #
    @1
    cT
    cU
    @8
    @0
    cH
    cK
    cV
    cW
    chlt
    dvheveccl.h
    dvheveccl.t
    @11
    dvheveccl.u
    dvheveccl.v
    dvhelvbasei
    syl12anc
    wph
    @1
    vf
    cT
    @0
    cmpt
    #
    wne
    #
    @5
    wph
    @6
    @14
    dvheveccl.k
    cB
    cT
    vf
    @8
    cH
    cK
    @13
    cW
    dvheveccl.b
    dvheveccl.h
    dvheveccl.t
    @11
    @13
    eqid
    #
    tendo1ne0
    syl
    wph
    @2
    c.0
    @1
    @13
    wph
    @2
    c.0
    wceq
    #
    c.0
    @0
    @13
    cop
    #
    wceq
    #
    @1
    @13
    wceq
    #
    wph
    @6
    @18
    dvheveccl.k
    cB
    cT
    cU
    vf
    cH
    cK
    @13
    cW
    c.0
    dvheveccl.b
    dvheveccl.h
    dvheveccl.t
    dvheveccl.u
    dvheveccl.z
    @15
    dvh0g
    syl
    @16
    @18
    wa
    @2
    @17
    wceq
    #
    wph
    @19
    @2
    c.0
    @17
    eqtr
    wph
    @20
    @0
    @0
    wceq
    #
    @19
    wa
    #
    @19
    wph
    @7
    @9
    @20
    @22
    wb
    @10
    @12
    @0
    @1
    @0
    @13
    cT
    @8
    opthg
    syl2anc
    @21
    @19
    simpr
    syl6bi
    syl5
    mpan2d
    necon3d
    mpd
    @2
    cV
    c.0
    eldifsn
    sylanbrc
    syl5eqel
end
