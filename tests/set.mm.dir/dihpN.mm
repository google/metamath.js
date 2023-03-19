include "clsa.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "c0g.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dihat.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "chlt.mm"
include "catm.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "lhpocnel2.mm"
include "syl.mm"
include "ltrniotaidvalN.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "wne.mm"
include "simpld.mm"
include "tendoid.mm"
include "eqtr2d.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resiexg.mm"
include "mp1i.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "opelopabg.mm"
include "mpbir2and.mm"
include "cdic.mm"
include "dihvalcqat.mm"
include "dicval.mm"
include "eleqtrd.mm"
include "simprd.mm"
include "dvh0g.mm"
include "ax-mp.mm"
include "cmpt.mm"
include "cltrn.mm"
include "mptex.mm"
include "opth2.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "mpd.mm"
include "lsatel.mm"

theorem dihpN
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cO: class O
  let cW: class W
  let vg: setvar g
  let vs: setvar s
  assume dihp.b: |- B = ( Base ` K )
  assume dihp.h: |- H = ( LHyp ` K )
  assume dihp.p: |- P = ( ( oc ` K ) ` W )
  assume dihp.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihp.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihp.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume dihp.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihp.n: |- N = ( LSpan ` U )
  assume dihp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihp.s: |- ( ph -> ( S e. E /\ S =/= O ) )

  disjoint B f
  disjoint H f
  disjoint K f
  disjoint P f
  disjoint T f
  disjoint W f
  disjoint f g
  disjoint f s
  disjoint g s
  disjoint B g
  disjoint B s
  disjoint E g
  disjoint E s
  disjoint K g
  disjoint K s
  disjoint P g
  disjoint P s
  disjoint S g
  disjoint S s
  disjoint T g
  disjoint T s
  disjoint W g
  disjoint W s
  assert |- ( ph -> ( I ` P ) = ( N ` { <. ( _I |` B ) , S >. } ) )

  proof
    wph
    cU
    clsa
    cfv
    #
    cP
    cI
    cfv
    #
    cN
    cU
    cid
    cB
    cres
    #
    cS
    cop
    #
    cU
    c0g
    cfv
    #
    @4
    eqid
    #
    dihp.n
    @0
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dihp.h
    dihp.u
    dihp.k
    dvhlvec
    wph
    @0
    cP
    cU
    cH
    cI
    cK
    cW
    dihp.h
    dihp.p
    dihp.i
    dihp.u
    @6
    dihp.k
    dihat
    wph
    @3
    vg
    cv
    #
    cP
    vf
    cv
    cfv
    cP
    wceq
    vf
    cT
    crio
    #
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @9
    cE
    wcel
    #
    wa
    #
    vg
    vs
    copab
    #
    @1
    wph
    @3
    @14
    wcel
    #
    @2
    @8
    cS
    cfv
    #
    wceq
    #
    cS
    cE
    wcel
    #
    wph
    @16
    @2
    cS
    cfv
    #
    @2
    wph
    @8
    @2
    cS
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cK
    catm
    cfv
    #
    wcel
    cP
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    wa
    #
    @8
    @2
    wceq
    dihp.k
    wph
    @20
    @23
    dihp.k
    @21
    cP
    cH
    cK
    @22
    cW
    @22
    eqid
    #
    @21
    eqid
    #
    dihp.h
    dihp.p
    lhpocnel2
    syl
    #
    @21
    cB
    cP
    cT
    vf
    @8
    cH
    cK
    @22
    cW
    dihp.b
    @24
    @25
    dihp.h
    dihp.t
    @8
    eqid
    ltrniotaidvalN
    syl2anc
    fveq2d
    wph
    @20
    @18
    @19
    @2
    wceq
    dihp.k
    wph
    @18
    cS
    cO
    wne
    #
    dihp.s
    simpld
    #
    cB
    cS
    cE
    cH
    cK
    cW
    dihp.b
    dihp.h
    dihp.e
    tendoid
    syl2anc
    eqtr2d
    @28
    wph
    @2
    cvv
    wcel
    #
    @18
    @15
    @17
    @18
    wa
    #
    wb
    cB
    cvv
    wcel
    #
    @29
    wph
    cB
    cK
    cbs
    cfv
    cvv
    dihp.b
    cK
    cbs
    fvex
    eqeltri
    #
    cB
    cvv
    resiexg
    #
    mp1i
    @28
    @13
    @2
    @10
    wceq
    #
    @12
    wa
    @30
    vg
    vs
    @2
    cS
    cvv
    cE
    @7
    @2
    wceq
    @11
    @34
    @12
    @7
    @2
    @10
    eqeq1
    anbi1d
    @9
    cS
    wceq
    #
    @34
    @17
    @12
    @18
    @35
    @10
    @16
    @2
    @8
    @9
    cS
    fveq1
    eqeq2d
    @9
    cS
    cE
    eleq1
    anbi12d
    opelopabg
    syl2anc
    mpbir2and
    wph
    @1
    cP
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    #
    @14
    wph
    @20
    @23
    @1
    @37
    wceq
    dihp.k
    @26
    @21
    cP
    cH
    cI
    @36
    cK
    @22
    cW
    @24
    @25
    dihp.h
    @36
    eqid
    #
    dihp.i
    dihvalcqat
    syl2anc
    wph
    @20
    @23
    @37
    @14
    wceq
    dihp.k
    @26
    @21
    cP
    cP
    cT
    vg
    vf
    cE
    cH
    @36
    cK
    @22
    chlt
    cW
    vs
    @24
    @25
    dihp.h
    dihp.p
    dihp.t
    dihp.e
    @38
    dicval
    syl2anc
    eqtr2d
    eleqtrd
    wph
    @27
    @3
    @4
    wne
    wph
    @18
    @27
    dihp.s
    simprd
    wph
    @3
    @4
    cS
    cO
    wph
    @3
    @4
    wceq
    @3
    @2
    cO
    cop
    #
    wceq
    #
    cS
    cO
    wceq
    #
    wph
    @4
    @39
    @3
    wph
    @20
    @4
    @39
    wceq
    dihp.k
    cB
    cT
    cU
    vf
    cH
    cK
    cO
    cW
    @4
    dihp.b
    dihp.h
    dihp.t
    dihp.u
    @5
    dihp.o
    dvh0g
    syl
    eqeq2d
    @40
    @2
    @2
    wceq
    @41
    @2
    cS
    @2
    cO
    @31
    @29
    @32
    @33
    ax-mp
    cO
    vf
    cT
    @2
    cmpt
    cvv
    dihp.o
    vf
    cT
    @2
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dihp.t
    cW
    @42
    fvex
    eqeltri
    mptex
    eqeltri
    opth2
    simprbi
    syl6bi
    necon3d
    mpd
    lsatel
end
