include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cgcd.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "0z.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "breq2.mm"
include "bi2anan9.mm"
include "anidm.mm"
include "syl6bb.mm"
include "mpbiri.mm"
include "oveq12.mm"
include "gcd0val.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "adantl.mm"
include "wn.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "w3a.mm"
include "cle.mm"
include "wi.mm"
include "cpr.mm"
include "wral.mm"
include "eqid.mm"
include "gcdcllem3.mm"
include "simp2d.mm"
include "gcdn0val.mm"
include "pm2.61dan.mm"

theorem gcddvds
  let cM: class M
  let cN: class N
  let cK: class K
  let vn: setvar n
  let vz: setvar z


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( M gcd N ) || M /\ ( M gcd N ) || N ) )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    cdvds
    wbr
    #
    @4
    cN
    cdvds
    wbr
    #
    wa
    #
    @3
    @7
    @0
    @3
    @7
    cc0
    cM
    cdvds
    wbr
    #
    cc0
    cN
    cdvds
    wbr
    #
    wa
    #
    @3
    @10
    cc0
    cc0
    cdvds
    wbr
    #
    cc0
    cz
    wcel
    @11
    0z
    cc0
    dvds0
    ax-mp
    @3
    @10
    @11
    @11
    wa
    @11
    @1
    @8
    @11
    @2
    @9
    @11
    cM
    cc0
    cc0
    cdvds
    breq2
    cN
    cc0
    cc0
    cdvds
    breq2
    bi2anan9
    @11
    anidm
    syl6bb
    mpbiri
    @3
    @5
    @8
    @6
    @9
    @3
    @4
    cc0
    cM
    cdvds
    @3
    @4
    cc0
    cc0
    cgcd
    co
    cc0
    cM
    cc0
    cN
    cc0
    cgcd
    oveq12
    gcd0val
    syl6eq
    #
    breq1d
    @3
    @4
    cc0
    cN
    cdvds
    @12
    breq1d
    anbi12d
    mpbird
    adantl
    @0
    @3
    wn
    wa
    #
    @7
    vn
    cv
    #
    cM
    cdvds
    wbr
    @14
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
    cM
    cdvds
    wbr
    #
    @16
    cN
    cdvds
    wbr
    #
    wa
    #
    @13
    @16
    cn
    wcel
    @19
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
    @16
    cle
    wbr
    wi
    vn
    @15
    @14
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
    @20
    eqid
    @15
    eqid
    gcdcllem3
    simp2d
    @13
    @5
    @17
    @6
    @18
    @13
    @4
    @16
    cM
    cdvds
    vn
    cM
    cN
    gcdn0val
    #
    breq1d
    @13
    @4
    @16
    cN
    cdvds
    @21
    breq1d
    anbi12d
    mpbird
    pm2.61dan
end
