include "wss.mm"
include "cfv.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "cdvh.mm"
include "cbs.mm"
include "adantr.mm"
include "crn.mm"
include "eqid.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "dochss.mm"
include "syl3anc.mm"
include "dochcl.mm"
include "wceq.mm"
include "dochoc.mm"
include "3sstr3d.mm"
include "impbida.mm"

theorem dochord
  let wph: wff ph
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume doch11.h: |- H = ( LHyp ` K )
  assume doch11.i: |- I = ( ( DIsoH ` K ) ` W )
  assume doch11.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume doch11.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume doch11.x: |- ( ph -> X e. ran I )
  assume doch11.y: |- ( ph -> Y e. ran I )


  assert |- ( ph -> ( X C_ Y <-> ( ._|_ ` Y ) C_ ( ._|_ ` X ) ) )

  proof
    wph
    cX
    cY
    wss
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wss
    #
    wph
    @0
    wa
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cY
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    wss
    #
    @0
    @3
    wph
    @4
    @0
    doch11.k
    adantr
    wph
    @7
    @0
    wph
    @4
    cY
    cI
    crn
    #
    wcel
    #
    @7
    doch11.k
    doch11.y
    @5
    cH
    cI
    cK
    @6
    cW
    cY
    doch11.h
    @5
    eqid
    #
    doch11.i
    @6
    eqid
    #
    dihrnss
    syl2anc
    adantr
    wph
    @0
    simpr
    @5
    cH
    cK
    c.pe
    @6
    cW
    cX
    cY
    doch11.h
    @10
    @11
    doch11.o
    dochss
    syl3anc
    wph
    @3
    wa
    #
    @2
    c.pe
    cfv
    #
    @1
    c.pe
    cfv
    #
    cX
    cY
    @12
    @4
    @2
    @6
    wss
    #
    @3
    @13
    @14
    wss
    wph
    @4
    @3
    doch11.k
    adantr
    wph
    @15
    @3
    wph
    @4
    @2
    @8
    wcel
    #
    @15
    doch11.k
    wph
    @4
    cX
    @6
    wss
    #
    @16
    doch11.k
    wph
    @4
    cX
    @8
    wcel
    #
    @17
    doch11.k
    doch11.x
    @5
    cH
    cI
    cK
    @6
    cW
    cX
    doch11.h
    @10
    doch11.i
    @11
    dihrnss
    syl2anc
    @5
    cH
    cI
    cK
    c.pe
    @6
    cW
    cX
    doch11.h
    doch11.i
    @10
    @11
    doch11.o
    dochcl
    syl2anc
    @5
    cH
    cI
    cK
    @6
    cW
    @2
    doch11.h
    @10
    doch11.i
    @11
    dihrnss
    syl2anc
    adantr
    wph
    @3
    simpr
    @5
    cH
    cK
    c.pe
    @6
    cW
    @1
    @2
    doch11.h
    @10
    @11
    doch11.o
    dochss
    syl3anc
    wph
    @13
    cX
    wceq
    #
    @3
    wph
    @4
    @18
    @19
    doch11.k
    doch11.x
    cH
    cI
    cK
    c.pe
    cW
    cX
    doch11.h
    doch11.i
    doch11.o
    dochoc
    syl2anc
    adantr
    wph
    @14
    cY
    wceq
    #
    @3
    wph
    @4
    @9
    @20
    doch11.k
    doch11.y
    cH
    cI
    cK
    c.pe
    cW
    cY
    doch11.h
    doch11.i
    doch11.o
    dochoc
    syl2anc
    adantr
    3sstr3d
    impbida
end
