include "cz.mm"
include "wcel.mm"
include "cword.mm"
include "ccsh.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cc0.mm"
include "cconcat.mm"
include "cshword.mm"
include "swrdcl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "cshnz.mm"
include "wrd0.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem cshwcl
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( W cyclShift N ) e. Word V )

  proof
    cN
    cz
    wcel
    #
    cW
    cV
    cword
    #
    wcel
    #
    cW
    cN
    ccsh
    co
    #
    @1
    wcel
    #
    wi
    @2
    @0
    @4
    @2
    @0
    wa
    @3
    cW
    cN
    cW
    chash
    cfv
    #
    cmo
    co
    #
    @5
    cop
    csubstr
    co
    #
    cW
    cc0
    @6
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    @1
    cN
    cV
    cW
    cshword
    @2
    @9
    @1
    wcel
    #
    @0
    @2
    @7
    @1
    wcel
    @8
    @1
    wcel
    @10
    cV
    cW
    @6
    @5
    swrdcl
    cV
    cW
    cc0
    @6
    swrdcl
    cV
    @7
    @8
    ccatcl
    syl2anc
    adantr
    eqeltrd
    expcom
    @0
    wn
    #
    @4
    @2
    @11
    @3
    c0
    @1
    cN
    cW
    cshnz
    cV
    wrd0
    syl6eqel
    a1d
    pm2.61i
end
