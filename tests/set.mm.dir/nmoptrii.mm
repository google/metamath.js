include "chos.mm"
include "co.mm"
include "cnop.mm"
include "cfv.mm"
include "caddc.mm"
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
include "bdopf.mm"
include "ax-mp.mm"
include "hoaddcli.mm"
include "cr.mm"
include "nmopre.mm"
include "readdcli.mm"
include "rexri.mm"
include "nmopub.mm"
include "mp2an.mm"
include "wa.mm"
include "hoscli.mm"
include "normcl.mm"
include "syl.mm"
include "adantr.mm"
include "ffvelrni.mm"
include "readdcld.mm"
include "a1i.mm"
include "cva.mm"
include "wceq.mm"
include "hosval.mm"
include "mp3an12.mm"
include "fveq2d.mm"
include "norm-ii.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "nmoplb.mm"
include "mp3an1.mm"
include "le2add.mm"
include "mpanr12.mm"
include "mp2and.mm"
include "letrd.mm"
include "ex.mm"
include "mprgbir.mm"

theorem nmoptrii
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( normop ` ( S +op T ) ) <_ ( ( normop ` S ) + ( normop ` T ) )

  proof
    cS
    cT
    chos
    co
    #
    cnop
    cfv
    cS
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vx
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    @5
    @0
    cfv
    #
    cno
    cfv
    #
    @3
    cle
    wbr
    #
    wi
    #
    vx
    chil
    chil
    chil
    @0
    wf
    @3
    cxr
    wcel
    @4
    @10
    vx
    chil
    wral
    wb
    cS
    cT
    cS
    cbo
    wcel
    #
    chil
    chil
    cS
    wf
    #
    nmoptri.1
    cS
    bdopf
    ax-mp
    #
    cT
    cbo
    wcel
    #
    chil
    chil
    cT
    wf
    #
    nmoptri.2
    cT
    bdopf
    ax-mp
    #
    hoaddcli
    @3
    @1
    @2
    @11
    @1
    cr
    wcel
    #
    nmoptri.1
    cS
    nmopre
    ax-mp
    #
    @14
    @2
    cr
    wcel
    #
    nmoptri.2
    cT
    nmopre
    ax-mp
    #
    readdcli
    #
    rexri
    vx
    @3
    @0
    nmopub
    mp2an
    @5
    chil
    wcel
    #
    @6
    @9
    @22
    @6
    wa
    #
    @8
    @5
    cS
    cfv
    #
    cno
    cfv
    #
    @5
    cT
    cfv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @3
    @22
    @8
    cr
    wcel
    #
    @6
    @22
    @7
    chil
    wcel
    @29
    @5
    cS
    cT
    @13
    @16
    hoscli
    @7
    normcl
    syl
    adantr
    @22
    @28
    cr
    wcel
    @6
    @22
    @25
    @27
    @22
    @24
    chil
    wcel
    #
    @25
    cr
    wcel
    #
    chil
    chil
    @5
    cS
    @13
    ffvelrni
    #
    @24
    normcl
    syl
    #
    @22
    @26
    chil
    wcel
    #
    @27
    cr
    wcel
    #
    chil
    chil
    @5
    cT
    @16
    ffvelrni
    #
    @26
    normcl
    syl
    #
    readdcld
    adantr
    @3
    cr
    wcel
    @23
    @21
    a1i
    @22
    @8
    @28
    cle
    wbr
    @6
    @22
    @8
    @24
    @26
    cva
    co
    #
    cno
    cfv
    #
    @28
    cle
    @22
    @7
    @38
    cno
    @12
    @15
    @22
    @7
    @38
    wceq
    @13
    @16
    @5
    cS
    cT
    hosval
    mp3an12
    fveq2d
    @22
    @30
    @34
    @39
    @28
    cle
    wbr
    @32
    @36
    @24
    @26
    norm-ii
    syl2anc
    eqbrtrd
    adantr
    @23
    @25
    @1
    cle
    wbr
    #
    @27
    @2
    cle
    wbr
    #
    @28
    @3
    cle
    wbr
    #
    @12
    @22
    @6
    @40
    @13
    @5
    cS
    nmoplb
    mp3an1
    @15
    @22
    @6
    @41
    @16
    @5
    cT
    nmoplb
    mp3an1
    @22
    @40
    @41
    wa
    @42
    wi
    #
    @6
    @22
    @31
    @35
    @43
    @33
    @37
    @31
    @35
    wa
    @17
    @19
    @43
    @18
    @20
    @25
    @27
    @1
    @2
    le2add
    mpanr12
    syl2anc
    adantr
    mp2and
    letrd
    ex
    mprgbir
end
