include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "ccsh.mm"
include "oveq2.mm"
include "cvtx.mm"
include "cword.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "cshwn.mm"
include "syl.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "wn.mm"
include "cfzo.mm"
include "wi.mm"
include "df-ne.mm"
include "fzofzim.mm"
include "expcom.mm"
include "syl5bir.mm"
include "adantl.mm"
include "impcom.mm"
include "clwwisshclwws.mm"
include "syl2anc.mm"
include "pm2.61ian.mm"

theorem clwwisshclwwsn
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( ( W e. ( ClWWalks ` G ) /\ N e. ( 0 ... ( # ` W ) ) ) -> ( W cyclShift N ) e. ( ClWWalks ` G ) )

  proof
    cN
    cW
    chash
    cfv
    #
    wceq
    #
    cW
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    cN
    cc0
    @0
    cfz
    co
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    @2
    wcel
    #
    @1
    @5
    wa
    @6
    cW
    @2
    @1
    @5
    @6
    cW
    @0
    ccsh
    co
    #
    cW
    cN
    @0
    cW
    ccsh
    oveq2
    @3
    @8
    cW
    wceq
    #
    @4
    @3
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @9
    @3
    cG
    cvv
    wcel
    @11
    cW
    c0
    wne
    cG
    @10
    cW
    @10
    eqid
    clwwlkbp
    simp2d
    @10
    cW
    cshwn
    syl
    adantr
    sylan9eq
    @1
    @3
    @4
    simprl
    eqeltrd
    @1
    wn
    #
    @5
    wa
    @3
    cN
    cc0
    @0
    cfzo
    co
    wcel
    #
    @7
    @12
    @3
    @4
    simprl
    @5
    @12
    @13
    @4
    @12
    @13
    wi
    @3
    @12
    cN
    @0
    wne
    #
    @4
    @13
    cN
    @0
    df-ne
    @14
    @4
    @13
    cN
    @0
    fzofzim
    expcom
    syl5bir
    adantl
    impcom
    cG
    cN
    cW
    clwwisshclwws
    syl2anc
    pm2.61ian
end
