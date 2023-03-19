include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrex.mm"
include "cn0.mm"
include "nnpw2p.mm"
include "wa.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "mpan.mm"
include "elfzonn0.mm"
include "nnnn0addcl.mm"
include "syl2an.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "impbii.mm"

theorem nnpw2pb
  let vi: setvar i
  let cN: class N
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint N i
  disjoint N r
  disjoint i r
  disjoint k x
  assert |- ( N e. NN <-> E. i e. NN0 E. r e. ( 0 ..^ ( 2 ^ i ) ) N = ( ( 2 ^ i ) + r ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    vi
    cv
    #
    cexp
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cc0
    @2
    cfzo
    co
    #
    wrex
    vi
    cn0
    wrex
    vi
    cN
    vr
    nnpw2p
    @5
    @0
    vi
    vr
    cn0
    @6
    @1
    cn0
    wcel
    #
    @3
    @6
    wcel
    #
    wa
    @0
    @5
    @4
    cn
    wcel
    #
    @7
    @2
    cn
    wcel
    #
    @3
    cn0
    wcel
    @9
    @8
    c2
    cn
    wcel
    @7
    @10
    2nn
    c2
    @1
    nnexpcl
    mpan
    @3
    @2
    elfzonn0
    @2
    @3
    nnnn0addcl
    syl2an
    cN
    @4
    cn
    eleq1
    syl5ibrcom
    rexlimivv
    impbii
end
