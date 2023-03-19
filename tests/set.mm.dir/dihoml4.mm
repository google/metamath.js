include "cfv.mm"
include "cin.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "syl.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "ineq1d.mm"
include "fveq2d.mm"
include "dochssv.mm"
include "dochoccl.mm"
include "mpbird.mm"
include "dochss.mm"
include "syl3anc.mm"
include "sseqtrd.mm"
include "dihoml4c.mm"
include "eqtr3d.mm"

theorem dihoml4
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihoml4.h: |- H = ( LHyp ` K )
  assume dihoml4.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihoml4.s: |- S = ( LSubSp ` U )
  assume dihoml4.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dihoml4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihoml4.x: |- ( ph -> X e. S )
  assume dihoml4.y: |- ( ph -> Y e. S )
  assume dihoml4.c: |- ( ph -> ( ._|_ ` ( ._|_ ` Y ) ) = Y )
  assume dihoml4.l: |- ( ph -> X C_ Y )


  assert |- ( ph -> ( ( ._|_ ` ( ( ._|_ ` X ) i^i Y ) ) i^i Y ) = ( ._|_ ` ( ._|_ ` X ) ) )

  proof
    wph
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    cin
    #
    c.pe
    cfv
    #
    cY
    cin
    @0
    cY
    cin
    #
    c.pe
    cfv
    #
    cY
    cin
    @1
    wph
    @4
    @6
    cY
    wph
    @3
    @5
    c.pe
    wph
    @2
    @0
    cY
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
    @2
    @0
    wceq
    dihoml4.k
    wph
    @7
    cX
    cU
    cbs
    cfv
    #
    wss
    #
    @10
    dihoml4.k
    wph
    cX
    cS
    wcel
    @12
    dihoml4.x
    cS
    cX
    @11
    cU
    @11
    eqid
    #
    dihoml4.s
    lssss
    syl
    #
    cU
    cH
    @8
    cK
    c.pe
    @11
    cW
    cX
    dihoml4.h
    @8
    eqid
    #
    dihoml4.u
    @13
    dihoml4.o
    dochcl
    syl2anc
    cH
    @8
    cK
    c.pe
    cW
    @0
    dihoml4.h
    @15
    dihoml4.o
    dochoc
    syl2anc
    ineq1d
    fveq2d
    ineq1d
    wph
    cH
    @8
    cK
    c.pe
    cW
    @1
    cY
    dihoml4.h
    @15
    dihoml4.o
    dihoml4.k
    wph
    @7
    @0
    @11
    wss
    #
    @1
    @9
    wcel
    dihoml4.k
    wph
    @7
    @12
    @16
    dihoml4.k
    @14
    cU
    cH
    cK
    c.pe
    @11
    cW
    cX
    dihoml4.h
    dihoml4.u
    @13
    dihoml4.o
    dochssv
    syl2anc
    #
    cU
    cH
    @8
    cK
    c.pe
    @11
    cW
    @0
    dihoml4.h
    @15
    dihoml4.u
    @13
    dihoml4.o
    dochcl
    syl2anc
    wph
    cY
    @9
    wcel
    cY
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    wceq
    dihoml4.c
    wph
    cU
    cH
    @8
    cK
    c.pe
    @11
    cW
    cY
    dihoml4.h
    @15
    dihoml4.u
    @13
    dihoml4.o
    dihoml4.k
    wph
    cY
    cS
    wcel
    cY
    @11
    wss
    #
    dihoml4.y
    cS
    cY
    @11
    cU
    @13
    dihoml4.s
    lssss
    syl
    #
    dochoccl
    mpbird
    wph
    @1
    @19
    cY
    wph
    @7
    @16
    @18
    @0
    wss
    #
    @1
    @19
    wss
    dihoml4.k
    @17
    wph
    @7
    @20
    cX
    cY
    wss
    @22
    dihoml4.k
    @21
    dihoml4.l
    cU
    cH
    cK
    c.pe
    @11
    cW
    cX
    cY
    dihoml4.h
    dihoml4.u
    @13
    dihoml4.o
    dochss
    syl3anc
    cU
    cH
    cK
    c.pe
    @11
    cW
    @18
    @0
    dihoml4.h
    dihoml4.u
    @13
    dihoml4.o
    dochss
    syl3anc
    dihoml4.c
    sseqtrd
    dihoml4c
    eqtr3d
end
