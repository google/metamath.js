include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "inss1.mm"
include "filsspw.mm"
include "adantr.mm"
include "syl5ss.mm"
include "0nelfil.mm"
include "sseli.mm"
include "nsyl.mm"
include "filtop.mm"
include "adantl.mm"
include "elind.mm"
include "3jca.mm"
include "simpll.mm"
include "simpr2.mm"
include "syl.mm"
include "simpr1.mm"
include "elpwid.mm"
include "simpr3.mm"
include "filss.mm"
include "syl13anc.mm"
include "simplr.mm"
include "inss2.mm"
include "3exp2.mm"
include "imp.mm"
include "rexlimdv.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "anim12i.mm"
include "filin.mm"
include "3expb.mm"
include "syl2an.mm"
include "simpr.mm"
include "ralrimivva.mm"
include "isfil2.mm"
include "syl3anbrc.mm"

theorem infil
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( Fil ` X ) /\ G e. ( Fil ` X ) ) -> ( F i^i G ) e. ( Fil ` X ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cin
    #
    cX
    cpw
    #
    wss
    #
    c0
    @4
    wcel
    #
    wn
    #
    cX
    @4
    wcel
    #
    w3a
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vy
    @4
    wrex
    @11
    @4
    wcel
    #
    wi
    #
    vx
    @5
    wral
    @11
    @10
    cin
    #
    @4
    wcel
    #
    vy
    @4
    wral
    vx
    @4
    wral
    @4
    @0
    wcel
    @3
    @6
    @8
    @9
    @3
    @4
    cF
    @5
    cF
    cG
    inss1
    #
    @1
    cF
    @5
    wss
    @2
    cF
    cX
    filsspw
    adantr
    syl5ss
    @3
    c0
    cF
    wcel
    #
    @7
    @1
    @18
    wn
    @2
    cF
    cX
    0nelfil
    adantr
    @4
    cF
    c0
    @17
    sseli
    nsyl
    @3
    cF
    cG
    cX
    @1
    cX
    cF
    wcel
    @2
    cF
    cX
    filtop
    adantr
    @2
    cX
    cG
    wcel
    @1
    cG
    cX
    filtop
    adantl
    elind
    3jca
    @3
    @14
    vx
    @5
    @3
    @11
    @5
    wcel
    #
    wa
    @12
    @13
    vy
    @4
    @3
    @19
    @10
    @4
    wcel
    #
    @12
    @13
    wi
    wi
    @3
    @19
    @20
    @12
    @13
    @3
    @19
    @20
    @12
    w3a
    #
    wa
    #
    cF
    cG
    @11
    @22
    @1
    @10
    cF
    wcel
    #
    @11
    cX
    wss
    #
    @12
    @11
    cF
    wcel
    #
    @1
    @2
    @21
    simpll
    @22
    @20
    @23
    @3
    @19
    @20
    @12
    simpr2
    #
    @4
    cF
    @10
    @17
    sseli
    #
    syl
    @22
    @11
    cX
    @3
    @19
    @20
    @12
    simpr1
    elpwid
    #
    @3
    @19
    @20
    @12
    simpr3
    #
    @10
    @11
    cF
    cX
    filss
    syl13anc
    @22
    @2
    @10
    cG
    wcel
    #
    @24
    @12
    @11
    cG
    wcel
    #
    @1
    @2
    @21
    simplr
    @22
    @20
    @30
    @26
    @4
    cG
    @10
    cF
    cG
    inss2
    #
    sseli
    #
    syl
    @28
    @29
    @10
    @11
    cG
    cX
    filss
    syl13anc
    elind
    3exp2
    imp
    rexlimdv
    ralrimiva
    @3
    @16
    vx
    vy
    @4
    @4
    @3
    @13
    @20
    wa
    #
    wa
    cF
    cG
    @15
    @3
    @1
    @25
    @23
    wa
    @15
    cF
    wcel
    #
    @34
    @1
    @2
    simpl
    @13
    @25
    @20
    @23
    @4
    cF
    @11
    @17
    sseli
    @27
    anim12i
    @1
    @25
    @23
    @35
    @11
    @10
    cF
    cX
    filin
    3expb
    syl2an
    @3
    @2
    @31
    @30
    wa
    @15
    cG
    wcel
    #
    @34
    @1
    @2
    simpr
    @13
    @31
    @20
    @30
    @4
    cG
    @11
    @32
    sseli
    @33
    anim12i
    @2
    @31
    @30
    @36
    @11
    @10
    cG
    cX
    filin
    3expb
    syl2an
    elind
    ralrimivva
    vx
    vy
    @4
    cX
    isfil2
    syl3anbrc
end
