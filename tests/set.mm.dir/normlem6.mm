include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "c4.mm"
include "cmul.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "caddc.mm"
include "cmin.mm"
include "wtru.mm"
include "cr.mm"
include "wcel.mm"
include "csp.mm"
include "chil.mm"
include "hiidrcl.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "a1i.mm"
include "normlem2.mm"
include "cv.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "0re.mm"
include "elimel.mm"
include "normlem5.mm"
include "dedth.mm"
include "adantl.mm"
include "discr.mm"
include "trud.mm"
include "resqcli.mm"
include "4re.mm"
include "remulcli.mm"
include "lesubadd2i.mm"
include "mpbi.mm"
include "recni.mm"
include "addid1i.mm"
include "breqtri.mm"
include "wb.mm"
include "sqge0i.mm"
include "4pos.mm"
include "ltleii.mm"
include "hiidge0.mm"
include "breqtrri.mm"
include "mulge0i.mm"
include "mp2an.mm"
include "sqrtlei.mm"
include "absrei.mm"
include "sqrtmulii.mm"
include "sqrt4.mm"
include "oveq12i.mm"
include "eqtr2i.mm"
include "3brtr4i.mm"

theorem normlem6
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H
  assume normlem2.4: |- B = -u ( ( ( * ` S ) x. ( F .ih G ) ) + ( S x. ( G .ih F ) ) )
  assume normlem3.5: |- A = ( G .ih G )
  assume normlem3.6: |- C = ( F .ih F )
  assume normlem6.7: |- ( abs ` S ) = 1


  assert |- ( abs ` B ) <_ ( 2 x. ( ( sqrt ` A ) x. ( sqrt ` C ) ) )

  proof
    cB
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    c4
    cA
    cC
    cmul
    co
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cB
    cabs
    cfv
    c2
    cA
    csqrt
    cfv
    cC
    csqrt
    cfv
    cmul
    co
    #
    cmul
    co
    #
    cle
    @0
    @3
    cle
    wbr
    #
    @1
    @4
    cle
    wbr
    #
    @0
    @3
    cc0
    caddc
    co
    #
    @3
    cle
    @0
    @3
    cmin
    co
    cc0
    cle
    wbr
    #
    @0
    @9
    cle
    wbr
    @10
    wtru
    vx
    cA
    cB
    cC
    cA
    cr
    wcel
    wtru
    cA
    cG
    cG
    csp
    co
    #
    cr
    normlem3.5
    cG
    chil
    wcel
    #
    @11
    cr
    wcel
    normlem1.3
    cG
    hiidrcl
    ax-mp
    eqeltri
    #
    a1i
    cB
    cr
    wcel
    wtru
    cB
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    normlem2.4
    normlem2
    #
    a1i
    cC
    cr
    wcel
    wtru
    cC
    cF
    cF
    csp
    co
    #
    cr
    normlem3.6
    cF
    chil
    wcel
    #
    @15
    cr
    wcel
    normlem1.2
    cF
    hiidrcl
    ax-mp
    eqeltri
    #
    a1i
    vx
    cv
    #
    cr
    wcel
    #
    cc0
    cA
    @18
    c2
    cexp
    co
    #
    cmul
    co
    #
    cB
    @18
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    cle
    wbr
    #
    wtru
    @19
    @25
    cc0
    cA
    @19
    @18
    cc0
    cif
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    cB
    @26
    cmul
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    cle
    wbr
    @18
    cc0
    @18
    @26
    wceq
    #
    @24
    @31
    cc0
    cle
    @32
    @23
    @30
    cC
    caddc
    @32
    @21
    @28
    @22
    @29
    caddc
    @32
    @20
    @27
    cA
    cmul
    @18
    @26
    c2
    cexp
    oveq1
    oveq2d
    @18
    @26
    cB
    cmul
    oveq2
    oveq12d
    oveq1d
    breq2d
    cA
    cB
    cC
    @26
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    normlem2.4
    normlem3.5
    normlem3.6
    @18
    cc0
    cr
    0re
    elimel
    normlem6.7
    normlem5
    dedth
    adantl
    discr
    trud
    @0
    @3
    cc0
    cB
    @14
    resqcli
    #
    c4
    @2
    4re
    cA
    cC
    @13
    @17
    remulcli
    #
    remulcli
    #
    0re
    lesubadd2i
    mpbi
    @3
    @3
    @35
    recni
    addid1i
    breqtri
    cc0
    @0
    cle
    wbr
    cc0
    @3
    cle
    wbr
    #
    @7
    @8
    wb
    cB
    @14
    sqge0i
    cc0
    c4
    cle
    wbr
    cc0
    @2
    cle
    wbr
    #
    @36
    cc0
    c4
    0re
    4re
    4pos
    ltleii
    #
    cc0
    cA
    cle
    wbr
    cc0
    cC
    cle
    wbr
    @37
    cc0
    @11
    cA
    cle
    @12
    cc0
    @11
    cle
    wbr
    normlem1.3
    cG
    hiidge0
    ax-mp
    normlem3.5
    breqtrri
    #
    cc0
    @15
    cC
    cle
    @16
    cc0
    @15
    cle
    wbr
    normlem1.2
    cF
    hiidge0
    ax-mp
    normlem3.6
    breqtrri
    #
    cA
    cC
    @13
    @17
    mulge0i
    mp2an
    #
    c4
    @2
    4re
    @34
    mulge0i
    mp2an
    @0
    @3
    @33
    @35
    sqrtlei
    mp2an
    mpbi
    cB
    @14
    absrei
    @4
    c4
    csqrt
    cfv
    #
    @2
    csqrt
    cfv
    #
    cmul
    co
    @6
    c4
    @2
    4re
    @34
    @38
    @41
    sqrtmulii
    @42
    c2
    @43
    @5
    cmul
    sqrt4
    cA
    cC
    @13
    @17
    @39
    @40
    sqrtmulii
    oveq12i
    eqtr2i
    3brtr4i
end
