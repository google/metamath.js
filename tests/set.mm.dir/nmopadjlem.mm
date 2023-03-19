include "cado.mm"
include "cfv.mm"
include "cnop.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "cbo.mm"
include "adjbdln.mm"
include "bdopf.mm"
include "mp2b.mm"
include "nmopxr.mm"
include "nmopub.mm"
include "mp2an.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "ffvelrni.mm"
include "normcl.mm"
include "syl.mm"
include "adantr.mm"
include "nmopre.mm"
include "ax-mp.mm"
include "remulcl.mm"
include "sylancr.mm"
include "1re.mm"
include "remulcli.mm"
include "a1i.mm"
include "nmopadjlei.mm"
include "cc0.mm"
include "nmopge0.mm"
include "pm3.2i.mm"
include "lemul2a.mm"
include "mp3anl3.mm"
include "mpanl2.mm"
include "sylan.mm"
include "letrd.mm"
include "recni.mm"
include "mulid1i.mm"
include "syl6breq.mm"
include "ex.mm"
include "mprgbir.mm"

theorem nmopadjlem
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vy: setvar y
  assume nmopadjle.1: |- T e. BndLinOp


  assert |- ( normop ` ( adjh ` T ) ) <_ ( normop ` T )

  proof
    cT
    cado
    cfv
    #
    cnop
    cfv
    cT
    cnop
    cfv
    #
    cle
    wbr
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @3
    @0
    cfv
    #
    cno
    cfv
    #
    @1
    cle
    wbr
    #
    wi
    #
    vy
    chil
    chil
    chil
    @0
    wf
    #
    @1
    cxr
    wcel
    #
    @2
    @9
    vy
    chil
    wral
    wb
    cT
    cbo
    wcel
    #
    @0
    cbo
    wcel
    @10
    nmopadjle.1
    cT
    adjbdln
    @0
    bdopf
    mp2b
    #
    @12
    chil
    chil
    cT
    wf
    #
    @11
    nmopadjle.1
    cT
    bdopf
    #
    cT
    nmopxr
    mp2b
    vy
    @1
    @0
    nmopub
    mp2an
    @3
    chil
    wcel
    #
    @5
    @8
    @16
    @5
    wa
    #
    @7
    @1
    c1
    cmul
    co
    #
    @1
    cle
    @17
    @7
    @1
    @4
    cmul
    co
    #
    @18
    @16
    @7
    cr
    wcel
    #
    @5
    @16
    @6
    chil
    wcel
    @20
    chil
    chil
    @3
    @0
    @13
    ffvelrni
    @6
    normcl
    syl
    adantr
    @16
    @19
    cr
    wcel
    #
    @5
    @16
    @1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @21
    @12
    @22
    nmopadjle.1
    cT
    nmopre
    ax-mp
    #
    @3
    normcl
    #
    @1
    @4
    remulcl
    sylancr
    adantr
    @18
    cr
    wcel
    @17
    @1
    c1
    @24
    1re
    remulcli
    a1i
    @16
    @7
    @19
    cle
    wbr
    @5
    @3
    cT
    nmopadjle.1
    nmopadjlei
    adantr
    @16
    @23
    @5
    @19
    @18
    cle
    wbr
    #
    @25
    @23
    c1
    cr
    wcel
    #
    @5
    @26
    1re
    @23
    @27
    @22
    cc0
    @1
    cle
    wbr
    #
    wa
    @5
    @26
    @22
    @28
    @24
    @12
    @14
    @28
    nmopadjle.1
    @15
    cT
    nmopge0
    mp2b
    pm3.2i
    @4
    c1
    @1
    lemul2a
    mp3anl3
    mpanl2
    sylan
    letrd
    @1
    @1
    @24
    recni
    mulid1i
    syl6breq
    ex
    mprgbir
end
