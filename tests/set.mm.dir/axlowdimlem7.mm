include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cop.mm"
include "csn.mm"
include "cfz.mm"
include "co.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "cun.mm"
include "cee.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "eqid.mm"
include "3ex.mm"
include "negex.mm"
include "fsn.mm"
include "mpbir.mm"
include "neg1rr.mm"
include "snssi.mm"
include "ax-mp.mm"
include "fss.mm"
include "mp2an.mm"
include "0re.mm"
include "fconst6.mm"
include "pm3.2i.mm"
include "disjdif.mm"
include "fun2.mm"
include "cle.mm"
include "wbr.mm"
include "eluzle.mm"
include "1le3.mm"
include "jctil.mm"
include "cz.mm"
include "wb.mm"
include "eluzelz.mm"
include "3z.mm"
include "1z.mm"
include "elfz.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpbird.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "feq2d.mm"
include "mpbii.mm"
include "cn.mm"
include "eluzge3nn.mm"
include "elee.mm"
include "syl5eqel.mm"

theorem axlowdimlem7
  let cP: class P
  let cN: class N
  assume axlowdimlem7.1: |- P = ( { <. 3 , -u 1 >. } u. ( ( ( 1 ... N ) \ { 3 } ) X. { 0 } ) )


  assert |- ( N e. ( ZZ>= ` 3 ) -> P e. ( EE ` N ) )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    cP
    c3
    c1
    cneg
    #
    cop
    csn
    #
    c1
    cN
    cfz
    co
    #
    c3
    csn
    #
    cdif
    #
    cc0
    csn
    cxp
    #
    cun
    #
    cN
    cee
    cfv
    #
    axlowdimlem7.1
    @0
    @7
    @8
    wcel
    #
    @3
    cr
    @7
    wf
    #
    @0
    @4
    @5
    cun
    #
    cr
    @7
    wf
    #
    @10
    @4
    cr
    @2
    wf
    #
    @5
    cr
    @6
    wf
    #
    wa
    @4
    @5
    cin
    c0
    wceq
    @12
    @13
    @14
    @4
    @1
    csn
    #
    @2
    wf
    #
    @15
    cr
    wss
    #
    @13
    @16
    @2
    @2
    wceq
    @2
    eqid
    c3
    @1
    @2
    3ex
    c1
    negex
    fsn
    mpbir
    @1
    cr
    wcel
    @17
    neg1rr
    @1
    cr
    snssi
    ax-mp
    @4
    @15
    cr
    @2
    fss
    mp2an
    @5
    cc0
    cr
    0re
    fconst6
    pm3.2i
    @4
    @3
    disjdif
    @4
    @5
    cr
    @2
    @6
    fun2
    mp2an
    @0
    @11
    @3
    cr
    @7
    @0
    @4
    @3
    wss
    @11
    @3
    wceq
    @0
    c3
    @3
    @0
    c3
    @3
    wcel
    #
    c1
    c3
    cle
    wbr
    #
    c3
    cN
    cle
    wbr
    #
    wa
    #
    @0
    @20
    @19
    c3
    cN
    eluzle
    1le3
    jctil
    @0
    cN
    cz
    wcel
    #
    @18
    @21
    wb
    #
    c3
    cN
    eluzelz
    c3
    cz
    wcel
    c1
    cz
    wcel
    @22
    @23
    3z
    1z
    c3
    c1
    cN
    elfz
    mp3an12
    syl
    mpbird
    snssd
    @4
    @3
    undif
    sylib
    feq2d
    mpbii
    @0
    cN
    cn
    wcel
    @9
    @10
    wb
    cN
    eluzge3nn
    @7
    cN
    elee
    syl
    mpbird
    syl5eqel
end
