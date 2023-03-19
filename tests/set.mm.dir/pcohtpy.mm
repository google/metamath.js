include "cpco.mm"
include "cfv.mm"
include "co.mm"
include "cii.mm"
include "ccn.mm"
include "wcel.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "cphtpc.mm"
include "wbr.mm"
include "w3a.mm"
include "isphtpc.mm"
include "sylib.mm"
include "simp1d.mm"
include "pcocn.mm"
include "simp2d.mm"
include "c1.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "phtpc01.mm"
include "syl.mm"
include "simprd.mm"
include "simpld.mm"
include "3eqtr3d.mm"
include "cv.mm"
include "wex.mm"
include "simp3d.mm"
include "n0.mm"
include "eeanv.mm"
include "sylanbrc.mm"
include "cicc.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt2.mm"
include "adantr.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "pcohtpylem.mm"
include "ne0i.mm"
include "ex.mm"
include "exlimdvv.mm"
include "mpd.mm"
include "syl3anbrc.mm"

theorem pcohtpy
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cN: class N
  let vz: setvar z
  let cP: class P
  assume pcohtpy.4: |- ( ph -> ( F ` 1 ) = ( G ` 0 ) )
  assume pcohtpy.5: |- ( ph -> F ( ~=ph ` J ) H )
  assume pcohtpy.6: |- ( ph -> G ( ~=ph ` J ) K )


  assert |- ( ph -> ( F ( *p ` J ) G ) ( ~=ph ` J ) ( H ( *p ` J ) K ) )

  proof
    wph
    cF
    cG
    cJ
    cpco
    cfv
    #
    co
    #
    cii
    cJ
    ccn
    co
    #
    wcel
    cH
    cK
    @0
    co
    #
    @2
    wcel
    @1
    @3
    cJ
    cphtpy
    cfv
    #
    co
    #
    c0
    wne
    #
    @1
    @3
    cJ
    cphtpc
    cfv
    #
    wbr
    wph
    cF
    cG
    cJ
    wph
    cF
    @2
    wcel
    #
    cH
    @2
    wcel
    #
    cF
    cH
    @4
    co
    #
    c0
    wne
    #
    wph
    cF
    cH
    @7
    wbr
    #
    @8
    @9
    @11
    w3a
    pcohtpy.5
    cF
    cH
    cJ
    isphtpc
    sylib
    #
    simp1d
    wph
    cG
    @2
    wcel
    #
    cK
    @2
    wcel
    #
    cG
    cK
    @4
    co
    #
    c0
    wne
    #
    wph
    cG
    cK
    @7
    wbr
    #
    @14
    @15
    @17
    w3a
    pcohtpy.6
    cG
    cK
    cJ
    isphtpc
    sylib
    #
    simp1d
    pcohtpy.4
    pcocn
    wph
    cH
    cK
    cJ
    wph
    @8
    @9
    @11
    @13
    simp2d
    wph
    @14
    @15
    @17
    @19
    simp2d
    wph
    c1
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    c1
    cH
    cfv
    #
    cc0
    cK
    cfv
    #
    pcohtpy.4
    wph
    cc0
    cF
    cfv
    cc0
    cH
    cfv
    wceq
    #
    @20
    @22
    wceq
    #
    wph
    @12
    @24
    @25
    wa
    pcohtpy.5
    cF
    cH
    cJ
    phtpc01
    syl
    simprd
    wph
    @21
    @23
    wceq
    #
    c1
    cG
    cfv
    c1
    cK
    cfv
    wceq
    #
    wph
    @18
    @26
    @27
    wa
    pcohtpy.6
    cG
    cK
    cJ
    phtpc01
    syl
    simpld
    3eqtr3d
    pcocn
    wph
    vm
    cv
    #
    @10
    wcel
    #
    vn
    cv
    #
    @16
    wcel
    #
    wa
    #
    vn
    wex
    vm
    wex
    #
    @6
    wph
    @29
    vm
    wex
    #
    @31
    vn
    wex
    #
    @33
    wph
    @11
    @34
    wph
    @8
    @9
    @11
    @13
    simp3d
    vm
    @10
    n0
    sylib
    wph
    @17
    @35
    wph
    @14
    @15
    @17
    @19
    simp3d
    vn
    @16
    n0
    sylib
    @29
    @31
    vm
    vn
    eeanv
    sylanbrc
    wph
    @32
    @6
    vm
    vn
    wph
    @32
    @6
    wph
    @32
    wa
    #
    vx
    vy
    cc0
    c1
    cicc
    co
    #
    @37
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    cle
    wbr
    c2
    @38
    cmul
    co
    #
    vy
    cv
    #
    @28
    co
    @39
    c1
    cmin
    co
    @40
    @30
    co
    cif
    cmpt2
    #
    @5
    wcel
    @6
    @36
    vx
    vy
    @41
    cF
    cG
    cH
    cJ
    cK
    @28
    @30
    wph
    @20
    @21
    wceq
    @32
    pcohtpy.4
    adantr
    wph
    @12
    @32
    pcohtpy.5
    adantr
    wph
    @18
    @32
    pcohtpy.6
    adantr
    @41
    eqid
    wph
    @29
    @31
    simprl
    wph
    @29
    @31
    simprr
    pcohtpylem
    @5
    @41
    ne0i
    syl
    ex
    exlimdvv
    mpd
    @1
    @3
    cJ
    isphtpc
    syl3anbrc
end
