include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "bezout.mm"
include "3adant1.mm"
include "wi.mm"
include "dvds2ln.mm"
include "3impia.mm"
include "3coml.mm"
include "simp3l.mm"
include "simp12.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "simp13.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "3expia.mm"
include "rexlimdvv.mm"
include "ex.mm"
include "mpid.mm"

theorem dvdsgcd
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || M /\ K || N ) -> K || ( M gcd N ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cM
    cdvds
    wbr
    cK
    cN
    cdvds
    wbr
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    vx
    cv
    #
    cmul
    co
    #
    cN
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    cK
    @5
    cdvds
    wbr
    #
    @1
    @2
    @12
    @0
    vx
    vy
    cM
    cN
    bezout
    3adant1
    @3
    @4
    @12
    @13
    wi
    @3
    @4
    wa
    @11
    @13
    vx
    vy
    cz
    cz
    @3
    @4
    @6
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    wa
    #
    @11
    @13
    wi
    @3
    @4
    @16
    w3a
    #
    @13
    @11
    cK
    @10
    cdvds
    wbr
    @17
    cK
    @6
    cM
    cmul
    co
    #
    @8
    cN
    cmul
    co
    #
    caddc
    co
    #
    @10
    cdvds
    @16
    @3
    @4
    cK
    @20
    cdvds
    wbr
    #
    @16
    @3
    @4
    @21
    @6
    @8
    cK
    cM
    cN
    dvds2ln
    3impia
    3coml
    @17
    @18
    @7
    @19
    @9
    caddc
    @17
    @14
    @1
    @18
    @7
    wceq
    #
    @3
    @4
    @14
    @15
    simp3l
    @0
    @1
    @2
    @4
    @16
    simp12
    @14
    @6
    cc
    wcel
    cM
    cc
    wcel
    @22
    @1
    @6
    zcn
    cM
    zcn
    @6
    cM
    mulcom
    syl2an
    syl2anc
    @17
    @15
    @2
    @19
    @9
    wceq
    #
    @3
    @4
    @14
    @15
    simp3r
    @0
    @1
    @2
    @4
    @16
    simp13
    @15
    @8
    cc
    wcel
    cN
    cc
    wcel
    @23
    @2
    @8
    zcn
    cN
    zcn
    @8
    cN
    mulcom
    syl2an
    syl2anc
    oveq12d
    breqtrd
    @5
    @10
    cK
    cdvds
    breq2
    syl5ibrcom
    3expia
    rexlimdvv
    ex
    mpid
end
