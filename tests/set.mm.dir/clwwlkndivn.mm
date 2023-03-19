include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cv.mm"
include "ccsh.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "copab.mm"
include "cqs.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "cdvds.mm"
include "cz.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfn.mm"
include "cn0.mm"
include "eqid.mm"
include "fusgrvtxfi.mm"
include "adantr.mm"
include "qerclwwlknfi.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0zd.mm"
include "prmz.mm"
include "adantl.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "fusgrhashclwwlkn.mm"
include "breqtrrd.mm"

theorem clwwlkndivn
  let cG: class G
  let cN: class N
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u


  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> N || ( # ` ( N ClWWalksN G ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cN
    cN
    cG
    cclwwlkn
    co
    #
    vt
    cv
    #
    @3
    wcel
    vu
    cv
    #
    @3
    wcel
    @4
    @5
    vn
    cv
    ccsh
    co
    wceq
    vn
    cc0
    cN
    cfz
    co
    wrex
    w3a
    vt
    vu
    copab
    #
    cqs
    #
    chash
    cfv
    #
    cN
    cmul
    co
    #
    @3
    chash
    cfv
    cdvds
    @2
    @8
    cz
    wcel
    cN
    cz
    wcel
    #
    cN
    @9
    cdvds
    wbr
    @2
    @8
    @2
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    @7
    cfn
    wcel
    @8
    cn0
    wcel
    @0
    @12
    @1
    cG
    @11
    @11
    eqid
    fusgrvtxfi
    adantr
    vu
    vt
    @6
    vn
    cG
    cN
    @3
    @3
    eqid
    #
    @6
    eqid
    #
    qerclwwlknfi
    @7
    hashcl
    3syl
    nn0zd
    @1
    @10
    @0
    cN
    prmz
    adantl
    @8
    cN
    dvdsmul2
    syl2anc
    vu
    vt
    @6
    vn
    cG
    cN
    @3
    @13
    @14
    fusgrhashclwwlkn
    breqtrrd
end
