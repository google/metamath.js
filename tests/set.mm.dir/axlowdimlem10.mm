include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cee.mm"
include "cfv.mm"
include "cr.mm"
include "wf.mm"
include "caddc.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "cc0.mm"
include "wss.mm"
include "cop.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wf1o.mm"
include "ovex.mm"
include "1ex.mm"
include "f1osn.mm"
include "f1of.mm"
include "ax-mp.mm"
include "c0ex.mm"
include "fconst.mm"
include "pm3.2i.mm"
include "disjdif.mm"
include "fun.mm"
include "mp2an.mm"
include "feq1i.mm"
include "mpbir.mm"
include "1re.mm"
include "snssi.mm"
include "0re.mm"
include "unssi.mm"
include "fss.mm"
include "fznatpl1.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "feq2d.mm"
include "mpbii.mm"
include "wb.mm"
include "elee.mm"
include "adantr.mm"
include "mpbird.mm"

theorem axlowdimlem10
  let cQ: class Q
  let cI: class I
  let cN: class N
  assume axlowdimlem10.1: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )


  assert |- ( ( N e. NN /\ I e. ( 1 ... ( N - 1 ) ) ) -> Q e. ( EE ` N ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    wcel
    #
    wa
    #
    cQ
    cN
    cee
    cfv
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cr
    cQ
    wf
    #
    @2
    cI
    c1
    caddc
    co
    #
    csn
    #
    @4
    @7
    cdif
    #
    cun
    #
    cr
    cQ
    wf
    #
    @5
    @9
    c1
    csn
    #
    cc0
    csn
    #
    cun
    #
    cQ
    wf
    #
    @13
    cr
    wss
    @10
    @14
    @9
    @13
    @6
    c1
    cop
    csn
    #
    @8
    @12
    cxp
    #
    cun
    #
    wf
    #
    @7
    @11
    @15
    wf
    #
    @8
    @12
    @16
    wf
    #
    wa
    @7
    @8
    cin
    c0
    wceq
    @18
    @19
    @20
    @7
    @11
    @15
    wf1o
    @19
    @6
    c1
    cI
    c1
    caddc
    ovex
    1ex
    f1osn
    @7
    @11
    @15
    f1of
    ax-mp
    @8
    cc0
    c0ex
    fconst
    pm3.2i
    @7
    @4
    disjdif
    @7
    @8
    @11
    @12
    @15
    @16
    fun
    mp2an
    @9
    @13
    cQ
    @17
    axlowdimlem10.1
    feq1i
    mpbir
    @11
    @12
    cr
    c1
    cr
    wcel
    @11
    cr
    wss
    1re
    c1
    cr
    snssi
    ax-mp
    cc0
    cr
    wcel
    @12
    cr
    wss
    0re
    cc0
    cr
    snssi
    ax-mp
    unssi
    @9
    @13
    cr
    cQ
    fss
    mp2an
    @2
    @9
    @4
    cr
    cQ
    @2
    @7
    @4
    wss
    @9
    @4
    wceq
    @2
    @6
    @4
    cI
    cN
    fznatpl1
    snssd
    @7
    @4
    undif
    sylib
    feq2d
    mpbii
    @0
    @3
    @5
    wb
    @1
    cQ
    cN
    elee
    adantr
    mpbird
end
