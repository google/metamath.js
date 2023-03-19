include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wi.mm"
include "simp1.mm"
include "cops.mm"
include "omlop.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "eqid.mm"
include "omllaw.mm"
include "syl3anc.mm"
include "wb.mm"
include "oplecon3b.mm"
include "syl3an1.mm"
include "clat.mm"
include "omllat.mm"
include "latmcl.mm"
include "opcon3b.mm"
include "latjcom.mm"
include "col.mm"
include "omlol.mm"
include "oldmm2.mm"
include "opococ.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "eqeq2d.mm"
include "bitrd.mm"
include "3imtr4d.mm"

theorem omllaw4
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume omllaw4.b: |- B = ( Base ` K )
  assume omllaw4.l: |- .<_ = ( le ` K )
  assume omllaw4.m: |- ./\ = ( meet ` K )
  assume omllaw4.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X .<_ Y -> ( ( ._|_ ` ( ( ._|_ ` X ) ./\ Y ) ) ./\ Y ) = X ) )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    c.le
    wbr
    #
    @5
    @4
    @5
    @4
    c.pe
    cfv
    #
    c.an
    co
    #
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    @5
    cY
    c.an
    co
    #
    c.pe
    cfv
    #
    cY
    c.an
    co
    #
    cX
    wceq
    #
    @3
    @0
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @6
    @11
    wi
    @0
    @1
    @2
    simp1
    @3
    cK
    cops
    wcel
    #
    @2
    @17
    @0
    @1
    @19
    @2
    cK
    omlop
    #
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cK
    c.pe
    cY
    omllaw4.b
    omllaw4.o
    opoccl
    syl2anc
    #
    @3
    @19
    @1
    @18
    @21
    @0
    @1
    @2
    simp2
    #
    cB
    cK
    c.pe
    cX
    omllaw4.b
    omllaw4.o
    opoccl
    syl2anc
    #
    cB
    @9
    cK
    c.le
    c.an
    c.pe
    @4
    @5
    omllaw4.b
    omllaw4.l
    @9
    eqid
    #
    omllaw4.m
    omllaw4.o
    omllaw
    syl3anc
    @0
    @19
    @1
    @2
    @12
    @6
    wb
    @20
    cB
    cK
    c.le
    c.pe
    cX
    cY
    omllaw4.b
    omllaw4.l
    omllaw4.o
    oplecon3b
    syl3an1
    @3
    @16
    @5
    @15
    c.pe
    cfv
    #
    wceq
    #
    @11
    @3
    @19
    @15
    cB
    wcel
    #
    @1
    @16
    @28
    wb
    @21
    @3
    cK
    clat
    wcel
    #
    @14
    cB
    wcel
    #
    @2
    @29
    @0
    @1
    @30
    @2
    cK
    omllat
    3ad2ant1
    #
    @3
    @19
    @13
    cB
    wcel
    #
    @31
    @21
    @3
    @30
    @18
    @2
    @33
    @32
    @25
    @22
    cB
    cK
    c.an
    @5
    cY
    omllaw4.b
    omllaw4.m
    latmcl
    syl3anc
    #
    cB
    cK
    c.pe
    @13
    omllaw4.b
    omllaw4.o
    opoccl
    syl2anc
    @22
    cB
    cK
    c.an
    @14
    cY
    omllaw4.b
    omllaw4.m
    latmcl
    syl3anc
    @24
    cB
    cK
    c.pe
    @15
    cX
    omllaw4.b
    omllaw4.o
    opcon3b
    syl3anc
    @3
    @27
    @10
    @5
    @3
    @13
    @4
    @9
    co
    #
    @4
    @13
    @9
    co
    #
    @27
    @10
    @3
    @30
    @33
    @17
    @35
    @36
    wceq
    @32
    @34
    @23
    cB
    @9
    cK
    @13
    @4
    omllaw4.b
    @26
    latjcom
    syl3anc
    @3
    cK
    col
    wcel
    #
    @33
    @2
    @27
    @35
    wceq
    @0
    @1
    @37
    @2
    cK
    omlol
    3ad2ant1
    @34
    @22
    cB
    @9
    cK
    c.an
    c.pe
    @13
    cY
    omllaw4.b
    @26
    omllaw4.m
    omllaw4.o
    oldmm2
    syl3anc
    @3
    @8
    @13
    @4
    @9
    @3
    @7
    cY
    @5
    c.an
    @3
    @19
    @2
    @7
    cY
    wceq
    @21
    @22
    cB
    cK
    c.pe
    cY
    omllaw4.b
    omllaw4.o
    opococ
    syl2anc
    oveq2d
    oveq2d
    3eqtr4d
    eqeq2d
    bitrd
    3imtr4d
end
