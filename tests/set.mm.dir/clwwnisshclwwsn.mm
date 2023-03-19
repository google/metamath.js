include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "wa.mm"
include "ccsh.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "clwwlkclwwlkn.mm"
include "clwwlknlen.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "clwwisshclwwsn.mm"
include "syl2an2r.mm"
include "cvtx.mm"
include "cword.mm"
include "cz.mm"
include "eqid.mm"
include "clwwlknwrd.mm"
include "elfzelz.mm"
include "cshwlen.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqtrd.mm"
include "isclwwlkn.mm"
include "sylanbrc.mm"

theorem clwwnisshclwwsn
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W


  assert |- ( ( W e. ( N ClWWalksN G ) /\ M e. ( 0 ... N ) ) -> ( W cyclShift M ) e. ( N ClWWalksN G ) )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    #
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cW
    cM
    ccsh
    co
    #
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    @5
    chash
    cfv
    #
    cN
    wceq
    @5
    @0
    wcel
    @1
    cW
    @6
    wcel
    @3
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @7
    cG
    cN
    cW
    clwwlkclwwlkn
    @1
    @3
    @11
    @1
    @2
    @10
    cM
    @1
    cN
    @9
    cc0
    cfz
    @1
    @9
    cN
    cG
    cN
    cW
    clwwlknlen
    #
    eqcomd
    oveq2d
    eleq2d
    biimpa
    cG
    cM
    cW
    clwwisshclwwsn
    syl2an2r
    @4
    @8
    @9
    cN
    @1
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    cM
    cz
    wcel
    @8
    @9
    wceq
    @3
    cG
    cN
    @13
    cW
    @13
    eqid
    clwwlknwrd
    cM
    cc0
    cN
    elfzelz
    cM
    @13
    cW
    cshwlen
    syl2an
    @1
    @9
    cN
    wceq
    @3
    @12
    adantr
    eqtrd
    cG
    cN
    @5
    isclwwlkn
    sylanbrc
end
