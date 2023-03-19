include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "clcmf.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "cv.mm"
include "wral.mm"
include "cuz.mm"
include "wss.mm"
include "2eluzge1.mm"
include "fzss1.mm"
include "mp1i.mm"
include "sselda.mm"
include "cz.mm"
include "cfn.mm"
include "fzssz.mm"
include "fzfi.mm"
include "pm3.2i.mm"
include "dvdslcmf.mm"
include "breq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "elfzelz.mm"
include "iddvds.mm"
include "syl.mm"
include "adantl.mm"
include "wi.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem prmgaplcmlem1
  let cI: class I
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ I e. ( 2 ... N ) ) -> I || ( ( _lcm ` ( 1 ... N ) ) + I ) )

  proof
    cN
    cn
    wcel
    #
    cI
    c2
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cI
    c1
    cN
    cfz
    co
    #
    clcmf
    cfv
    #
    cdvds
    wbr
    #
    cI
    cI
    cdvds
    wbr
    #
    cI
    @5
    cI
    caddc
    co
    cdvds
    wbr
    #
    @3
    cI
    @4
    wcel
    vx
    cv
    #
    @5
    cdvds
    wbr
    #
    vx
    @4
    wral
    #
    @6
    @0
    @1
    @4
    cI
    c2
    c1
    cuz
    cfv
    wcel
    @1
    @4
    wss
    @0
    2eluzge1
    c2
    c1
    cN
    fzss1
    mp1i
    sselda
    @4
    cz
    wss
    #
    @4
    cfn
    wcel
    #
    wa
    #
    @11
    @3
    @12
    @13
    c1
    cN
    fzssz
    c1
    cN
    fzfi
    pm3.2i
    #
    vx
    @4
    dvdslcmf
    mp1i
    @10
    @6
    vx
    cI
    @4
    @9
    cI
    @5
    cdvds
    breq1
    rspcv
    sylc
    @2
    @7
    @0
    @2
    cI
    cz
    wcel
    #
    @7
    cI
    c2
    cN
    elfzelz
    #
    cI
    iddvds
    syl
    adantl
    @3
    @16
    @5
    cz
    wcel
    #
    @16
    @6
    @7
    wa
    @8
    wi
    @2
    @16
    @0
    @17
    adantl
    #
    @14
    @18
    @3
    @15
    @14
    @5
    @4
    lcmfcl
    nn0zd
    mp1i
    @19
    cI
    @5
    cI
    dvds2add
    syl3anc
    mp2and
end
