include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "cin.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "unssd.mm"
include "ssun1.mm"
include "a1i.mm"
include "dochss.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "ssind.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dochcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "dihmeetcl.mm"
include "syl12anc.mm"
include "dochoc.mm"
include "syl2anc.mm"
include "dochssv.mm"
include "ssinss1.mm"
include "syl.mm"
include "dochocss.mm"
include "unss12.mm"
include "inss1.mm"
include "inss2.mm"
include "sstrd.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem dochdmj1
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dochdmj1.h: |- H = ( LHyp ` K )
  assume dochdmj1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochdmj1.v: |- V = ( Base ` U )
  assume dochdmj1.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V /\ Y C_ V ) -> ( ._|_ ` ( X u. Y ) ) = ( ( ._|_ ` X ) i^i ( ._|_ ` Y ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    w3a
    #
    cX
    cY
    cun
    #
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    cin
    #
    @3
    @5
    @6
    @7
    @3
    @0
    @4
    cV
    wss
    #
    cX
    @4
    wss
    #
    @5
    @6
    wss
    @0
    @1
    @2
    simp1
    #
    @3
    cX
    cY
    cV
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    unssd
    #
    @10
    @3
    cX
    cY
    ssun1
    a1i
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    @4
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochss
    syl3anc
    @3
    @0
    @9
    cY
    @4
    wss
    #
    @5
    @7
    wss
    @11
    @12
    @13
    @3
    cY
    cX
    ssun2
    a1i
    cU
    cH
    cK
    c.pe
    cV
    cW
    cY
    @4
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochss
    syl3anc
    ssind
    @3
    @8
    @8
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @5
    @3
    @0
    @8
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
    @15
    @8
    wceq
    @11
    @3
    @0
    @6
    @17
    wcel
    #
    @7
    @17
    wcel
    #
    @18
    @11
    @0
    @1
    @19
    @2
    cU
    cH
    @16
    cK
    c.pe
    cV
    cW
    cX
    dochdmj1.h
    @16
    eqid
    #
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochcl
    3adant3
    @0
    @2
    @20
    @1
    cU
    cH
    @16
    cK
    c.pe
    cV
    cW
    cY
    dochdmj1.h
    @21
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochcl
    3adant2
    cH
    @16
    cK
    cW
    @6
    @7
    dochdmj1.h
    @21
    dihmeetcl
    syl12anc
    cH
    @16
    cK
    c.pe
    cW
    @8
    dochdmj1.h
    @21
    dochdmj1.o
    dochoc
    syl2anc
    @3
    @0
    @14
    cV
    wss
    #
    @4
    @14
    wss
    @15
    @5
    wss
    @11
    @3
    @0
    @8
    cV
    wss
    #
    @22
    @11
    @3
    @6
    cV
    wss
    #
    @23
    @0
    @1
    @24
    @2
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochssv
    3adant3
    #
    @6
    @7
    cV
    ssinss1
    syl
    cU
    cH
    cK
    c.pe
    cV
    cW
    @8
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochssv
    syl2anc
    @3
    @4
    @6
    c.pe
    cfv
    #
    @7
    c.pe
    cfv
    #
    cun
    #
    @14
    @3
    cX
    @26
    wss
    #
    cY
    @27
    wss
    #
    @4
    @28
    wss
    @0
    @1
    @29
    @2
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochocss
    3adant3
    @0
    @2
    @30
    @1
    cU
    cH
    cK
    c.pe
    cV
    cW
    cY
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochocss
    3adant2
    cX
    @26
    cY
    @27
    unss12
    syl2anc
    @3
    @26
    @27
    @14
    @3
    @0
    @24
    @8
    @6
    wss
    #
    @26
    @14
    wss
    @11
    @25
    @31
    @3
    @6
    @7
    inss1
    a1i
    cU
    cH
    cK
    c.pe
    cV
    cW
    @8
    @6
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochss
    syl3anc
    @3
    @0
    @7
    cV
    wss
    #
    @8
    @7
    wss
    #
    @27
    @14
    wss
    @11
    @0
    @2
    @32
    @1
    cU
    cH
    cK
    c.pe
    cV
    cW
    cY
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochssv
    3adant2
    @33
    @3
    @6
    @7
    inss2
    a1i
    cU
    cH
    cK
    c.pe
    cV
    cW
    @8
    @7
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochss
    syl3anc
    unssd
    sstrd
    cU
    cH
    cK
    c.pe
    cV
    cW
    @4
    @14
    dochdmj1.h
    dochdmj1.u
    dochdmj1.v
    dochdmj1.o
    dochss
    syl3anc
    eqsstr3d
    eqssd
end
