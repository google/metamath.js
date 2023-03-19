include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "wb.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "limsupbnd1.mm"

theorem limsupbnd1f
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  assume limsupbnd1f.1: |- F/_ j F
  assume limsupbnd1f.2: |- ( ph -> B C_ RR )
  assume limsupbnd1f.3: |- ( ph -> F : B --> RR* )
  assume limsupbnd1f.4: |- ( ph -> A e. RR* )
  assume limsupbnd1f.5: |- ( ph -> E. k e. RR A. j e. B ( k <_ j -> ( F ` j ) <_ A ) )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint B j
  disjoint B k
  disjoint F k
  disjoint A i
  disjoint A l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint B i
  disjoint B l
  disjoint F i
  disjoint F l
  disjoint i ph
  disjoint l ph
  assert |- ( ph -> ( limsup ` F ) <_ A )

  proof
    wph
    cA
    cB
    vl
    vi
    cF
    limsupbnd1f.2
    limsupbnd1f.3
    limsupbnd1f.4
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    #
    cA
    cle
    wbr
    #
    wi
    #
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    vi
    cv
    #
    vl
    cv
    #
    cle
    wbr
    #
    @8
    cF
    cfv
    #
    cA
    cle
    wbr
    #
    wi
    #
    vl
    cB
    wral
    #
    vi
    cr
    wrex
    limsupbnd1f.5
    @6
    @13
    vk
    vi
    cr
    @0
    @7
    wceq
    #
    @6
    @7
    @1
    cle
    wbr
    #
    @4
    wi
    #
    vj
    cB
    wral
    #
    @13
    @14
    @5
    @16
    vj
    cB
    @14
    @2
    @15
    @4
    @0
    @7
    @1
    cle
    breq1
    imbi1d
    ralbidv
    @17
    @13
    wb
    @14
    @16
    @12
    vj
    vl
    cB
    @16
    vl
    nfv
    @9
    @11
    vj
    @9
    vj
    nfv
    vj
    @10
    cA
    cle
    vj
    @8
    cF
    limsupbnd1f.1
    vj
    @8
    nfcv
    nffv
    vj
    cle
    nfcv
    vj
    cA
    nfcv
    nfbr
    nfim
    @1
    @8
    wceq
    #
    @15
    @9
    @4
    @11
    @1
    @8
    @7
    cle
    breq2
    @18
    @3
    @10
    cA
    cle
    @1
    @8
    cF
    fveq2
    breq1d
    imbi12d
    cbvral
    a1i
    bitrd
    cbvrexv
    sylib
    limsupbnd1
end
