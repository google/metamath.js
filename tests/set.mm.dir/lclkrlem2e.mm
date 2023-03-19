include "co.mm"
include "cfv.mm"
include "clsh.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "chlt.mm"
include "cdih.mm"
include "crn.mm"
include "adantr.mm"
include "wss.mm"
include "eldifad.mm"
include "snssd.mm"
include "eqid.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "cin.mm"
include "inidm.mm"
include "ineq2d.mm"
include "syl5eqr.mm"
include "dvhlmod.mm"
include "lkrin.mm"
include "eqsstrd.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "clspn.mm"
include "dochocsp.mm"
include "eqtr4d.mm"
include "clsa.mm"
include "lsatlspsn.mm"
include "dochsatshp.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "lshpcmp.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "dochoc1.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "ldualvaddcl.mm"
include "lkrshpor.mm"
include "mpjaod.mm"

theorem lclkrlem2e
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lclkrlem2e.h: |- H = ( LHyp ` K )
  assume lclkrlem2e.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2e.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2e.v: |- V = ( Base ` U )
  assume lclkrlem2e.z: |- .0. = ( 0g ` U )
  assume lclkrlem2e.f: |- F = ( LFnl ` U )
  assume lclkrlem2e.l: |- L = ( LKer ` U )
  assume lclkrlem2e.d: |- D = ( LDual ` U )
  assume lclkrlem2e.p: |- .+ = ( +g ` D )
  assume lclkrlem2e.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2e.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2e.e: |- ( ph -> E e. F )
  assume lclkrlem2e.g: |- ( ph -> G e. F )
  assume lclkrlem2e.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2e.ne: |- ( ph -> ( L ` E ) = ( L ` G ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cE
    cG
    c.pl
    co
    #
    cL
    cfv
    #
    cU
    clsh
    cfv
    #
    wcel
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    #
    @1
    cV
    wceq
    #
    wph
    @3
    @6
    wph
    @3
    wa
    #
    cX
    csn
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @10
    @5
    @1
    @8
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @10
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @12
    @10
    wceq
    wph
    @13
    @3
    lclkrlem2e.k
    adantr
    #
    @8
    @13
    @9
    cV
    wss
    #
    @15
    @16
    wph
    @17
    @3
    wph
    cX
    cV
    wph
    cX
    cV
    c.0
    csn
    lclkrlem2e.x
    eldifad
    snssd
    #
    adantr
    cU
    cH
    @14
    cK
    c.pe
    cV
    cW
    @9
    lclkrlem2e.h
    @14
    eqid
    #
    lclkrlem2e.u
    lclkrlem2e.v
    lclkrlem2e.o
    dochcl
    syl2anc
    cH
    @14
    cK
    c.pe
    cW
    @10
    lclkrlem2e.h
    @19
    lclkrlem2e.o
    dochoc
    syl2anc
    @8
    @11
    @4
    c.pe
    @8
    @10
    @1
    c.pe
    @8
    cE
    cL
    cfv
    #
    @10
    @1
    wph
    @20
    @10
    wceq
    @3
    lclkrlem2e.le
    adantr
    #
    @8
    @20
    @1
    wss
    #
    @20
    @1
    wceq
    wph
    @22
    @3
    wph
    @20
    @20
    cG
    cL
    cfv
    #
    cin
    #
    @1
    wph
    @20
    @20
    @20
    cin
    @24
    @20
    inidm
    wph
    @20
    @23
    @20
    lclkrlem2e.ne
    ineq2d
    syl5eqr
    wph
    cD
    c.pl
    cF
    cE
    cG
    cL
    cU
    lclkrlem2e.f
    lclkrlem2e.l
    lclkrlem2e.d
    lclkrlem2e.p
    wph
    cU
    cH
    cK
    cW
    lclkrlem2e.h
    lclkrlem2e.u
    lclkrlem2e.k
    dvhlmod
    #
    lclkrlem2e.e
    lclkrlem2e.g
    lkrin
    eqsstrd
    adantr
    @8
    @20
    @1
    @2
    cU
    @2
    eqid
    #
    wph
    cU
    clvec
    wcel
    @3
    wph
    cU
    cH
    cK
    cW
    lclkrlem2e.h
    lclkrlem2e.u
    lclkrlem2e.k
    dvhlvec
    #
    adantr
    @8
    @20
    @9
    cU
    clspn
    cfv
    #
    cfv
    #
    c.pe
    cfv
    #
    @2
    @8
    @20
    @10
    @30
    @21
    wph
    @30
    @10
    wceq
    @3
    wph
    cU
    cH
    cK
    @28
    c.pe
    cV
    cW
    @9
    lclkrlem2e.h
    lclkrlem2e.u
    lclkrlem2e.o
    lclkrlem2e.v
    @28
    eqid
    #
    lclkrlem2e.k
    @18
    dochocsp
    adantr
    eqtr4d
    @8
    cU
    clsa
    cfv
    #
    @29
    cU
    cH
    cK
    c.pe
    cW
    @2
    lclkrlem2e.h
    lclkrlem2e.u
    lclkrlem2e.o
    @32
    eqid
    #
    @26
    @16
    wph
    @29
    @32
    wcel
    @3
    wph
    @32
    @28
    cV
    cU
    cX
    c.0
    lclkrlem2e.v
    @31
    lclkrlem2e.z
    @33
    @25
    lclkrlem2e.x
    lsatlspsn
    adantr
    dochsatshp
    eqeltrd
    wph
    @3
    simpr
    lshpcmp
    mpbid
    eqtr3d
    #
    fveq2d
    fveq2d
    @34
    3eqtr3d
    ex
    wph
    @6
    @7
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    wceq
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    lclkrlem2e.h
    lclkrlem2e.u
    lclkrlem2e.o
    lclkrlem2e.v
    lclkrlem2e.k
    dochoc1
    @7
    @5
    @36
    @1
    cV
    @7
    @4
    @35
    c.pe
    @1
    cV
    c.pe
    fveq2
    fveq2d
    @7
    id
    eqeq12d
    syl5ibrcom
    wph
    cF
    @0
    @2
    cL
    cV
    cU
    lclkrlem2e.v
    @26
    lclkrlem2e.f
    lclkrlem2e.l
    @27
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2e.f
    lclkrlem2e.d
    lclkrlem2e.p
    @25
    lclkrlem2e.e
    lclkrlem2e.g
    ldualvaddcl
    lkrshpor
    mpjaod
end
