include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "caddc.mm"
include "zred.mm"
include "nn0red.mm"
include "readdcld.mm"
include "cr.mm"
include "nn0addge1.mm"
include "sylancom.mm"
include "lesub1dd.mm"
include "recnd.mm"
include "pncand.mm"
include "breqtrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"

theorem eluzmn
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN0 ) -> M e. ( ZZ>= ` ( M - N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cM
    cN
    cmin
    co
    #
    cz
    wcel
    @0
    @3
    cM
    cle
    wbr
    cM
    @3
    cuz
    cfv
    wcel
    @2
    cM
    cN
    @0
    @1
    simpl
    #
    @2
    cN
    @0
    @1
    simpr
    #
    nn0zd
    zsubcld
    @4
    @2
    @3
    cM
    cN
    caddc
    co
    #
    cN
    cmin
    co
    cM
    cle
    @2
    cM
    @6
    cN
    @2
    cM
    @4
    zred
    #
    @2
    cM
    cN
    @7
    @2
    cN
    @5
    nn0red
    #
    readdcld
    @8
    @0
    @1
    cM
    cr
    wcel
    cM
    @6
    cle
    wbr
    @7
    cM
    cN
    nn0addge1
    sylancom
    lesub1dd
    @2
    cM
    cN
    @2
    cM
    @7
    recnd
    @2
    cN
    @8
    recnd
    pncand
    breqtrd
    @3
    cM
    eluz2
    syl3anbrc
end
