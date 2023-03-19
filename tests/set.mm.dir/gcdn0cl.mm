include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "gcdn0val.mm"
include "w3a.mm"
include "cle.mm"
include "wi.mm"
include "cpr.mm"
include "wral.mm"
include "eqid.mm"
include "gcdcllem3.mm"
include "simp1d.mm"
include "eqeltrd.mm"

theorem gcdn0cl
  let cM: class M
  let cN: class N
  let cK: class K
  let vn: setvar n
  let vz: setvar z


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 /\ N = 0 ) ) -> ( M gcd N ) e. NN )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    wn
    wa
    #
    cM
    cN
    cgcd
    co
    vn
    cv
    #
    cM
    cdvds
    wbr
    @1
    cN
    cdvds
    wbr
    wa
    vn
    cz
    crab
    #
    cr
    clt
    csup
    #
    cn
    vn
    cM
    cN
    gcdn0val
    @0
    @3
    cn
    wcel
    @3
    cM
    cdvds
    wbr
    @3
    cN
    cdvds
    wbr
    wa
    cK
    cz
    wcel
    cK
    cM
    cdvds
    wbr
    cK
    cN
    cdvds
    wbr
    w3a
    cK
    @3
    cle
    wbr
    wi
    vn
    @2
    @1
    vz
    cv
    cdvds
    wbr
    vz
    cM
    cN
    cpr
    wral
    vn
    cz
    crab
    #
    vz
    cK
    cM
    cN
    @4
    eqid
    @2
    eqid
    gcdcllem3
    simp1d
    eqeltrd
end
