include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "ciso.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cop.mm"
include "wcel.mm"
include "wne.mm"
include "ccat.mm"
include "wceq.mm"
include "cicfval.mm"
include "syl.mm"
include "breqd.mm"
include "wb.mm"
include "df-br.mm"
include "a1i.mm"
include "fveq1d.mm"
include "neeq1d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "cbs.mm"
include "cxp.mm"
include "cvv.mm"
include "wfn.mm"
include "fvexd.mm"
include "sqxpexg.mm"
include "syl6eleq.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "isofn.mm"
include "fvn0elsuppb.mm"
include "syl3anc.mm"
include "3bitr3rd.mm"
include "3bitrd.mm"

theorem brcic
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  let cY: class Y
  assume cic.i: |- I = ( Iso ` C )
  assume cic.b: |- B = ( Base ` C )
  assume cic.c: |- ( ph -> C e. Cat )
  assume cic.x: |- ( ph -> X e. B )
  assume cic.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X ( ~=c ` C ) Y <-> ( X I Y ) =/= (/) ) )

  proof
    wph
    cX
    cY
    cC
    ccic
    cfv
    #
    wbr
    cX
    cY
    cC
    ciso
    cfv
    #
    c0
    csupp
    co
    #
    wbr
    #
    cX
    cY
    cop
    #
    @2
    wcel
    #
    cX
    cY
    cI
    co
    #
    c0
    wne
    #
    wph
    @0
    @2
    cX
    cY
    wph
    cC
    ccat
    wcel
    #
    @0
    @2
    wceq
    cic.c
    cC
    cicfval
    syl
    breqd
    @3
    @5
    wb
    wph
    cX
    cY
    @2
    df-br
    a1i
    wph
    @4
    cI
    cfv
    #
    c0
    wne
    @4
    @1
    cfv
    #
    c0
    wne
    #
    @7
    @5
    wph
    @9
    @10
    c0
    wph
    @4
    cI
    @1
    cI
    @1
    wceq
    wph
    cic.i
    a1i
    fveq1d
    neeq1d
    wph
    @9
    @6
    c0
    @9
    @6
    wceq
    wph
    @6
    @9
    cX
    cY
    cI
    df-ov
    eqcomi
    a1i
    neeq1d
    wph
    cC
    cbs
    cfv
    #
    @12
    cxp
    #
    cvv
    wcel
    #
    @4
    @13
    wcel
    #
    @1
    @13
    wfn
    #
    @11
    @5
    wb
    wph
    @12
    cvv
    wcel
    @14
    wph
    cC
    cbs
    fvexd
    @12
    cvv
    sqxpexg
    syl
    wph
    cX
    @12
    wcel
    cY
    @12
    wcel
    @15
    wph
    cX
    cB
    @12
    cic.x
    cic.b
    syl6eleq
    wph
    cY
    cB
    @12
    cic.y
    cic.b
    syl6eleq
    cX
    cY
    @12
    @12
    opelxp
    sylanbrc
    wph
    @8
    @16
    cic.c
    cC
    isofn
    syl
    @13
    @1
    cvv
    @4
    fvn0elsuppb
    syl3anc
    3bitr3rd
    3bitrd
end
