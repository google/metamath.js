include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "wrex.mm"
include "crio.mm"
include "wcel.mm"
include "eldifad.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "snssd.mm"
include "eqid.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lss0cl.mm"
include "lmodvs1.mm"
include "oveq2d.mm"
include "lmod0vlid.mm"
include "eqtr2d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wreu.mm"
include "wb.mm"
include "crg.mm"
include "lmodring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "clsm.mm"
include "clsh.mm"
include "clspn.mm"
include "dvhlvec.mm"
include "dochsnshp.mm"
include "dochexmidat.mm"
include "lshpsmreu.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem dochfl1
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochfl1.h: |- H = ( LHyp ` K )
  assume dochfl1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochfl1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochfl1.v: |- V = ( Base ` U )
  assume dochfl1.a: |- .+ = ( +g ` U )
  assume dochfl1.t: |- .x. = ( .s ` U )
  assume dochfl1.z: |- .0. = ( 0g ` U )
  assume dochfl1.d: |- D = ( Scalar ` U )
  assume dochfl1.r: |- R = ( Base ` D )
  assume dochfl1.i: |- .1. = ( 1r ` D )
  assume dochfl1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochfl1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume dochfl1.g: |- G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint .1. k
  disjoint .1. w
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint R k
  disjoint R v
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint V v
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint .0. w
  assert |- ( ph -> ( G ` X ) = .1. )

  proof
    wph
    cX
    cG
    cfv
    #
    cX
    vw
    cv
    #
    vk
    cv
    #
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    cX
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    c.1
    wph
    cX
    cV
    wcel
    #
    @0
    @9
    wceq
    wph
    cX
    cV
    c.0
    csn
    dochfl1.x
    eldifad
    #
    vv
    cX
    vv
    cv
    #
    @4
    wceq
    #
    vw
    @7
    wrex
    #
    vk
    cR
    crio
    @9
    cV
    cG
    @12
    cX
    wceq
    #
    @14
    @8
    vk
    cR
    @15
    @13
    @5
    vw
    @7
    @12
    cX
    @4
    eqeq1
    rexbidv
    riotabidv
    dochfl1.g
    @8
    vk
    cR
    riotaex
    fvmpt
    syl
    wph
    cX
    @1
    c.1
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @7
    wrex
    #
    @9
    c.1
    wceq
    #
    wph
    c.0
    @7
    wcel
    #
    cX
    c.0
    @16
    c.pl
    co
    #
    wceq
    #
    @19
    wph
    cU
    clmod
    wcel
    #
    @7
    cU
    clss
    cfv
    #
    wcel
    #
    @21
    wph
    cU
    cH
    cK
    cW
    dochfl1.h
    dochfl1.u
    dochfl1.k
    dvhlmod
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @6
    cV
    wss
    @26
    dochfl1.k
    wph
    cX
    cV
    @11
    snssd
    @25
    cU
    cH
    cK
    c.pe
    cV
    cW
    @6
    dochfl1.h
    dochfl1.u
    dochfl1.v
    @25
    eqid
    #
    dochfl1.o
    dochlss
    syl2anc
    @25
    @7
    cU
    c.0
    dochfl1.z
    @28
    lss0cl
    syl2anc
    wph
    @22
    c.0
    cX
    c.pl
    co
    #
    cX
    wph
    @16
    cX
    c.0
    c.pl
    wph
    @24
    @10
    @16
    cX
    wceq
    @27
    @11
    c.x
    c.1
    cD
    cV
    cU
    cX
    dochfl1.v
    dochfl1.d
    dochfl1.t
    dochfl1.i
    lmodvs1
    syl2anc
    oveq2d
    wph
    @24
    @10
    @29
    cX
    wceq
    @27
    @11
    c.pl
    cV
    cU
    cX
    c.0
    dochfl1.v
    dochfl1.a
    dochfl1.z
    lmod0vlid
    syl2anc
    eqtr2d
    @18
    @23
    vw
    c.0
    @7
    @1
    c.0
    wceq
    @17
    @22
    cX
    @1
    c.0
    @16
    c.pl
    oveq1
    eqeq2d
    rspcev
    syl2anc
    wph
    c.1
    cR
    wcel
    #
    @8
    vk
    cR
    wreu
    @19
    @20
    wb
    wph
    @24
    cD
    crg
    wcel
    @30
    @27
    cD
    cU
    dochfl1.d
    lmodring
    cR
    cD
    c.1
    dochfl1.r
    dochfl1.i
    ringidcl
    3syl
    wph
    vw
    cD
    c.pl
    cU
    clsm
    cfv
    #
    c.x
    @7
    vk
    cU
    clsh
    cfv
    #
    cR
    cU
    clspn
    cfv
    #
    cV
    cU
    cX
    cX
    dochfl1.v
    dochfl1.a
    @33
    eqid
    #
    @31
    eqid
    #
    @32
    eqid
    #
    wph
    cU
    cH
    cK
    cW
    dochfl1.h
    dochfl1.u
    dochfl1.k
    dvhlvec
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @32
    c.0
    dochfl1.h
    dochfl1.o
    dochfl1.u
    dochfl1.v
    dochfl1.z
    @36
    dochfl1.k
    dochfl1.x
    dochsnshp
    @11
    @11
    wph
    @31
    cU
    cH
    cK
    @33
    c.pe
    cV
    cW
    cX
    c.0
    dochfl1.h
    dochfl1.o
    dochfl1.u
    dochfl1.v
    dochfl1.z
    @34
    @35
    dochfl1.k
    dochfl1.x
    dochexmidat
    dochfl1.d
    dochfl1.r
    dochfl1.t
    lshpsmreu
    @8
    @19
    vk
    cR
    c.1
    @2
    c.1
    wceq
    #
    @5
    @18
    vw
    @7
    @37
    @4
    @17
    cX
    @37
    @3
    @16
    @1
    c.pl
    @2
    c.1
    cX
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    riota2
    syl2anc
    mpbid
    eqtrd
end
