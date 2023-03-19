include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "dochexmidlem5.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "doch0.mm"
include "syl.mm"
include "eqtrd.mm"
include "ineq1d.mm"
include "cdih.mm"
include "crn.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "wss.mm"
include "lssss.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "dochcl.mm"
include "eqeltrrd.mm"
include "dihsmatrn.mm"
include "syl5eqel.mm"
include "dihrnlss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "syl5eqss.mm"
include "dochoccl.mm"
include "mpbid.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmub1.mm"
include "syl6sseqr.mm"
include "dihoml4.mm"
include "sseqin2.mm"
include "sylib.mm"
include "3eqtr3rd.mm"

theorem dochexmidlem6
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  assume dochexmidlem1.h: |- H = ( LHyp ` K )
  assume dochexmidlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidlem1.v: |- V = ( Base ` U )
  assume dochexmidlem1.s: |- S = ( LSubSp ` U )
  assume dochexmidlem1.n: |- N = ( LSpan ` U )
  assume dochexmidlem1.p: |- .(+) = ( LSSum ` U )
  assume dochexmidlem1.a: |- A = ( LSAtoms ` U )
  assume dochexmidlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidlem1.x: |- ( ph -> X e. S )
  assume dochexmidlem6.pp: |- ( ph -> p e. A )
  assume dochexmidlem6.z: |- .0. = ( 0g ` U )
  assume dochexmidlem6.m: |- M = ( X .(+) p )
  assume dochexmidlem6.xn: |- ( ph -> X =/= { .0. } )
  assume dochexmidlem6.c: |- ( ph -> ( ._|_ ` ( ._|_ ` X ) ) = X )
  assume dochexmidlem6.pl: |- ( ph -> -. p C_ ( X .(+) ( ._|_ ` X ) ) )


  assert |- ( ph -> M = X )

  proof
    wph
    cM
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wph
    @0
    cM
    cin
    #
    c.pe
    cfv
    #
    cM
    cin
    cV
    cM
    cin
    #
    @1
    cM
    wph
    @3
    cV
    cM
    wph
    @3
    c.0
    csn
    #
    c.pe
    cfv
    #
    cV
    wph
    @2
    @5
    c.pe
    wph
    cA
    c.po
    cS
    cU
    cH
    cK
    cM
    cN
    c.pe
    cV
    cW
    cX
    c.0
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    dochexmidlem1.k
    dochexmidlem1.x
    dochexmidlem6.pp
    dochexmidlem6.z
    dochexmidlem6.m
    dochexmidlem6.xn
    dochexmidlem6.pl
    dochexmidlem5
    fveq2d
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @6
    cV
    wceq
    dochexmidlem1.k
    cU
    cH
    cK
    c.pe
    cV
    cW
    c.0
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.o
    dochexmidlem1.v
    dochexmidlem6.z
    doch0
    syl
    eqtrd
    ineq1d
    wph
    cS
    cU
    cH
    cK
    c.pe
    cW
    cX
    cM
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.s
    dochexmidlem1.o
    dochexmidlem1.k
    dochexmidlem1.x
    wph
    @7
    cM
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    cM
    cS
    wcel
    dochexmidlem1.k
    wph
    cM
    cX
    vp
    cv
    #
    c.po
    co
    #
    @9
    dochexmidlem6.m
    wph
    cA
    c.po
    @11
    cU
    cH
    @8
    cK
    cW
    cX
    dochexmidlem1.h
    @8
    eqid
    #
    dochexmidlem1.u
    dochexmidlem1.p
    dochexmidlem1.a
    dochexmidlem1.k
    wph
    @1
    cX
    @9
    dochexmidlem6.c
    wph
    @7
    @0
    cV
    wss
    #
    @1
    @9
    wcel
    dochexmidlem1.k
    wph
    @7
    cX
    cV
    wss
    #
    @14
    dochexmidlem1.k
    wph
    cX
    cS
    wcel
    #
    @15
    dochexmidlem1.x
    cS
    cX
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.o
    dochssv
    syl2anc
    cU
    cH
    @8
    cK
    c.pe
    cV
    cW
    @0
    dochexmidlem1.h
    @13
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.o
    dochcl
    syl2anc
    eqeltrrd
    dochexmidlem6.pp
    dihsmatrn
    syl5eqel
    #
    cS
    cU
    cH
    @8
    cK
    cW
    cM
    dochexmidlem1.h
    dochexmidlem1.u
    @13
    dochexmidlem1.s
    dihrnlss
    syl2anc
    wph
    @10
    cM
    c.pe
    cfv
    c.pe
    cfv
    cM
    wceq
    @17
    wph
    cU
    cH
    @8
    cK
    c.pe
    cV
    cW
    cM
    dochexmidlem1.h
    @13
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.o
    dochexmidlem1.k
    wph
    cM
    @12
    cV
    dochexmidlem6.m
    wph
    @12
    cS
    wcel
    #
    @12
    cV
    wss
    wph
    cU
    clmod
    wcel
    #
    @16
    @11
    cS
    wcel
    @18
    wph
    cU
    cH
    cK
    cW
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.k
    dvhlmod
    #
    dochexmidlem1.x
    wph
    cA
    cS
    @11
    cU
    dochexmidlem1.s
    dochexmidlem1.a
    @20
    dochexmidlem6.pp
    lsatlssel
    #
    c.po
    cS
    cX
    @11
    cU
    dochexmidlem1.s
    dochexmidlem1.p
    lsmcl
    syl3anc
    cS
    @12
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    syl5eqss
    #
    dochoccl
    mpbid
    wph
    cX
    @12
    cM
    wph
    cX
    cU
    csubg
    cfv
    #
    wcel
    @11
    @23
    wcel
    cX
    @12
    wss
    wph
    cS
    @23
    cX
    wph
    @19
    cS
    @23
    wss
    @20
    cS
    cU
    dochexmidlem1.s
    lsssssubg
    syl
    #
    dochexmidlem1.x
    sseldd
    wph
    cS
    @23
    @11
    @24
    @21
    sseldd
    c.po
    cX
    @11
    cU
    dochexmidlem1.p
    lsmub1
    syl2anc
    dochexmidlem6.m
    syl6sseqr
    dihoml4
    wph
    cM
    cV
    wss
    @4
    cM
    wceq
    @22
    cM
    cV
    sseqin2
    sylib
    3eqtr3rd
    dochexmidlem6.c
    eqtrd
end
