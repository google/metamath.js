include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "cn0.mm"
include "wss.mm"
include "nn0ex.mm"
include "ssex.mm"
include "syl.mm"
include "briunov2.mm"
include "syl2anc.mm"

theorem brmptiunrelexpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let vr: setvar r
  assume brmptiunrelexpd.c: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )
  assume brmptiunrelexpd.r: |- ( ph -> R e. _V )
  assume brmptiunrelexpd.n: |- ( ph -> N C_ NN0 )

  disjoint A n
  disjoint B n
  disjoint n r
  disjoint C n
  disjoint N n
  disjoint C r
  disjoint N r
  disjoint C N
  disjoint R n
  disjoint R r
  assert |- ( ph -> ( A ( C ` R ) B <-> E. n e. N A ( R ^r n ) B ) )

  proof
    wph
    cR
    cvv
    wcel
    cN
    cvv
    wcel
    #
    cA
    cB
    cR
    cC
    cfv
    wbr
    cA
    cB
    cR
    vn
    cv
    crelexp
    co
    wbr
    vn
    cN
    wrex
    wb
    brmptiunrelexpd.r
    wph
    cN
    cn0
    wss
    @0
    brmptiunrelexpd.n
    cN
    cn0
    nn0ex
    ssex
    syl
    cC
    cR
    cvv
    vn
    crelexp
    cN
    cvv
    cA
    cB
    vr
    brmptiunrelexpd.c
    briunov2
    syl2anc
end
