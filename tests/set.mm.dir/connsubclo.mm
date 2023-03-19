include "cin.mm"
include "wceq.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "eqid.mm"
include "ctop.mm"
include "wcel.mm"
include "cvv.mm"
include "ccld.mm"
include "cfv.mm"
include "cldrcl.mm"
include "syl.mm"
include "topopn.mm"
include "ssexd.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "cv.mm"
include "wrex.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wb.mm"
include "restcld.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "connclo.mm"
include "restuni.mm"
include "eqtr4d.mm"
include "sseqin2.mm"
include "sylibr.mm"

theorem connsubclo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume connsubclo.1: |- X = U. J
  assume connsubclo.3: |- ( ph -> A C_ X )
  assume connsubclo.4: |- ( ph -> ( J |`t A ) e. Conn )
  assume connsubclo.5: |- ( ph -> B e. J )
  assume connsubclo.6: |- ( ph -> ( B i^i A ) =/= (/) )
  assume connsubclo.7: |- ( ph -> B e. ( Clsd ` J ) )


  assert |- ( ph -> A C_ B )

  proof
    wph
    cB
    cA
    cin
    #
    cA
    wceq
    cA
    cB
    wss
    wph
    @0
    cJ
    cA
    crest
    co
    #
    cuni
    #
    cA
    wph
    @0
    @1
    @2
    @2
    eqid
    connsubclo.4
    wph
    cJ
    ctop
    wcel
    #
    cA
    cvv
    wcel
    cB
    cJ
    wcel
    @0
    @1
    wcel
    wph
    cB
    cJ
    ccld
    cfv
    #
    wcel
    #
    @3
    connsubclo.7
    cB
    cJ
    cldrcl
    syl
    #
    wph
    cA
    cX
    cJ
    wph
    @3
    cX
    cJ
    wcel
    @6
    cJ
    cX
    connsubclo.1
    topopn
    syl
    connsubclo.3
    ssexd
    connsubclo.5
    cB
    cA
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    connsubclo.6
    wph
    @0
    @1
    ccld
    cfv
    wcel
    #
    @0
    vx
    cv
    #
    cA
    cin
    #
    wceq
    #
    vx
    @4
    wrex
    #
    wph
    @5
    @0
    @0
    wceq
    #
    @11
    connsubclo.7
    @0
    eqid
    @10
    @12
    vx
    cB
    @4
    @8
    cB
    wceq
    @9
    @0
    @0
    @8
    cB
    cA
    ineq1
    eqeq2d
    rspcev
    sylancl
    wph
    @3
    cA
    cX
    wss
    #
    @7
    @11
    wb
    @6
    connsubclo.3
    vx
    @0
    cA
    cJ
    cX
    connsubclo.1
    restcld
    syl2anc
    mpbird
    connclo
    wph
    @3
    @13
    cA
    @2
    wceq
    @6
    connsubclo.3
    cA
    cJ
    cX
    connsubclo.1
    restuni
    syl2anc
    eqtr4d
    cA
    cB
    sseqin2
    sylibr
end
