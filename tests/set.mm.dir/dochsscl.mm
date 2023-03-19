include "wss.mm"
include "cfv.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "crn.mm"
include "dihrnss.mm"
include "simpr.mm"
include "dochss.mm"
include "syl3anc.mm"
include "wceq.mm"
include "dochoc.mm"
include "sseqtrd.mm"
include "dochocss.mm"
include "sstr.mm"
include "sylan.mm"
include "impbida.mm"

theorem dochsscl
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dochsscl.h: |- H = ( LHyp ` K )
  assume dochsscl.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsscl.v: |- V = ( Base ` U )
  assume dochsscl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochsscl.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsscl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsscl.x: |- ( ph -> X C_ V )
  assume dochsscl.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( X C_ Y <-> ( ._|_ ` ( ._|_ ` X ) ) C_ Y ) )

  proof
    wph
    cX
    cY
    wss
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    wss
    #
    wph
    @0
    wa
    #
    @2
    cY
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cY
    @4
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cV
    wss
    #
    @5
    @1
    wss
    #
    @2
    @6
    wss
    wph
    @7
    @0
    dochsscl.k
    adantr
    #
    @4
    @7
    cX
    cV
    wss
    #
    @8
    @10
    wph
    @11
    @0
    dochsscl.x
    adantr
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochsscl.h
    dochsscl.u
    dochsscl.v
    dochsscl.o
    dochssv
    syl2anc
    @4
    @7
    cY
    cV
    wss
    #
    @0
    @9
    @10
    wph
    @12
    @0
    wph
    @7
    cY
    cI
    crn
    wcel
    #
    @12
    dochsscl.k
    dochsscl.y
    cU
    cH
    cI
    cK
    cV
    cW
    cY
    dochsscl.h
    dochsscl.u
    dochsscl.i
    dochsscl.v
    dihrnss
    syl2anc
    adantr
    wph
    @0
    simpr
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    cY
    dochsscl.h
    dochsscl.u
    dochsscl.v
    dochsscl.o
    dochss
    syl3anc
    cU
    cH
    cK
    c.pe
    cV
    cW
    @5
    @1
    dochsscl.h
    dochsscl.u
    dochsscl.v
    dochsscl.o
    dochss
    syl3anc
    @4
    @7
    @13
    @6
    cY
    wceq
    @10
    wph
    @13
    @0
    dochsscl.y
    adantr
    cH
    cI
    cK
    c.pe
    cW
    cY
    dochsscl.h
    dochsscl.i
    dochsscl.o
    dochoc
    syl2anc
    sseqtrd
    wph
    cX
    @2
    wss
    #
    @3
    @0
    wph
    @7
    @11
    @14
    dochsscl.k
    dochsscl.x
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochsscl.h
    dochsscl.u
    dochsscl.v
    dochsscl.o
    dochocss
    syl2anc
    cX
    @2
    cY
    sstr
    sylan
    impbida
end
