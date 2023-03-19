include "cbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cxp.mm"
include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "isbnd3.mm"
include "wfn.mm"
include "wb.mm"
include "metf.mm"
include "adantr.mm"
include "ffn.mm"
include "ffnov.mm"
include "baib.mm"
include "3syl.mm"
include "0red.mm"
include "simplr.mm"
include "metcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "metge0.mm"
include "w3a.mm"
include "elicc2.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl22anc.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isbnd3b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let cN: class N
  let cP: class P
  let cR: class R
  let cS: class S
  let cY: class Y

  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint d m
  disjoint d r
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint M d
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint M r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint M s
  disjoint N d
  disjoint N r
  disjoint N y
  disjoint P d
  disjoint P r
  disjoint P y
  disjoint X d
  disjoint X m
  disjoint X r
  disjoint X s
  disjoint R r
  disjoint R x
  disjoint S r
  disjoint S x
  disjoint Y d
  disjoint Y r
  disjoint Y x
  disjoint Y y
  assert |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\ E. x e. RR A. y e. X A. z e. X ( y M z ) <_ x ) )

  proof
    cM
    cX
    cbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    #
    cX
    cX
    cxp
    #
    cc0
    vx
    cv
    #
    cicc
    co
    #
    cM
    wf
    #
    vx
    cr
    wrex
    #
    wa
    @0
    vy
    cv
    #
    vz
    cv
    #
    cM
    co
    #
    @2
    cle
    wbr
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    #
    wa
    vx
    cM
    cX
    isbnd3
    @0
    @5
    @11
    @0
    @4
    @10
    vx
    cr
    @0
    @2
    cr
    wcel
    #
    wa
    #
    @4
    @8
    @3
    wcel
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    @10
    @13
    @1
    cr
    cM
    wf
    #
    cM
    @1
    wfn
    #
    @4
    @15
    wb
    @0
    @16
    @12
    cM
    cX
    metf
    adantr
    @1
    cr
    cM
    ffn
    @4
    @17
    @15
    vy
    vz
    cX
    cX
    @3
    cM
    ffnov
    baib
    3syl
    @13
    @14
    @9
    vy
    vz
    cX
    cX
    @13
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    wa
    #
    cc0
    cr
    wcel
    #
    @12
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    @14
    @9
    wb
    @21
    0red
    @0
    @12
    @20
    simplr
    @0
    @20
    @23
    @12
    @0
    @18
    @19
    @23
    @6
    @7
    cM
    cX
    metcl
    3expb
    adantlr
    @0
    @20
    @24
    @12
    @0
    @18
    @19
    @24
    @6
    @7
    cM
    cX
    metge0
    3expb
    adantlr
    @22
    @12
    wa
    #
    @14
    @23
    @24
    wa
    #
    @9
    @25
    @14
    @23
    @24
    @9
    w3a
    @26
    @9
    wa
    cc0
    @2
    @8
    elicc2
    @23
    @24
    @9
    df-3an
    syl6bb
    baibd
    syl22anc
    2ralbidva
    bitrd
    rexbidva
    pm5.32i
    bitri
end
