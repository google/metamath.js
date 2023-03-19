include "wel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "adantr.mm"
include "cif.mm"
include "cop.mm"
include "cun.mm"
include "wcel.mm"
include "elun1.mm"
include "ad2antrl.mm"
include "unxpdomlem1.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "iffalse.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "biimpa.mm"
include "vex.mm"
include "ifex.mm"
include "opth.mm"
include "sylib.mm"
include "simprd.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "simpld.mm"
include "syl5ibr.mm"
include "syld.mm"
include "ad2antrr.mm"
include "equequ1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "pm2.65d.mm"
include "iffalsed.mm"
include "mt3d.mm"
include "3eqtr3d.mm"
include "mtand.mm"

theorem unxpdomlem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  assume unxpdomlem1.1: |- F = ( x e. ( a u. b ) |-> G )
  assume unxpdomlem1.2: |- G = if ( x e. a , <. x , if ( x = m , t , s ) >. , <. if ( x = t , n , m ) , x >. )
  assume unxpdomlem2.1: |- ( ph -> w e. ( a u. b ) )
  assume unxpdomlem2.2: |- ( ph -> -. m = n )
  assume unxpdomlem2.3: |- ( ph -> -. s = t )

  disjoint F w
  disjoint F z
  disjoint w z
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m w
  disjoint m x
  disjoint m z
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s z
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint w x
  disjoint x z
  assert |- ( ( ph /\ ( z e. a /\ -. w e. a ) ) -> -. ( F ` z ) = ( F ` w ) )

  proof
    wph
    vz
    va
    wel
    #
    vw
    va
    wel
    #
    wn
    #
    wa
    #
    wa
    #
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vs
    vt
    weq
    #
    wph
    @10
    wn
    @3
    unxpdomlem2.3
    adantr
    @4
    @9
    wa
    #
    vz
    vm
    weq
    #
    vt
    cv
    #
    vs
    cv
    #
    cif
    #
    @7
    @14
    @13
    @11
    @5
    vw
    vt
    weq
    #
    vn
    cv
    #
    vm
    cv
    #
    cif
    #
    wceq
    #
    @15
    @7
    wceq
    #
    @11
    @5
    @15
    cop
    #
    @19
    @7
    cop
    #
    wceq
    #
    @20
    @21
    wa
    @4
    @9
    @24
    @4
    @6
    @22
    @8
    @23
    @4
    @6
    @0
    @22
    vz
    vt
    weq
    @17
    @18
    cif
    @5
    cop
    #
    cif
    #
    @22
    @4
    @5
    va
    cv
    #
    vb
    cv
    #
    cun
    #
    wcel
    #
    @6
    @26
    wceq
    @0
    @30
    wph
    @2
    @5
    @27
    @28
    elun1
    ad2antrl
    vx
    vz
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    unxpdomlem1
    syl
    @0
    @26
    @22
    wceq
    wph
    @2
    @0
    @22
    @25
    iftrue
    ad2antrl
    eqtrd
    @4
    @8
    @1
    @7
    vw
    vm
    weq
    @13
    @14
    cif
    cop
    #
    @23
    cif
    #
    @23
    @4
    @7
    @29
    wcel
    #
    @8
    @32
    wceq
    wph
    @33
    @3
    unxpdomlem2.1
    adantr
    vx
    vw
    vt
    vm
    vn
    cF
    cG
    vs
    va
    vb
    unxpdomlem1.1
    unxpdomlem1.2
    unxpdomlem1
    syl
    @2
    @32
    @23
    wceq
    wph
    @0
    @1
    @31
    @23
    iffalse
    ad2antll
    eqtrd
    eqeq12d
    biimpa
    @5
    @15
    @19
    @7
    vz
    vex
    @12
    @13
    @14
    vt
    vex
    vs
    vex
    ifex
    opth
    sylib
    #
    simprd
    #
    @11
    @12
    @13
    @14
    @11
    @12
    vz
    vn
    weq
    #
    @11
    @12
    @16
    @36
    @12
    @15
    @13
    wceq
    @11
    @16
    @12
    @13
    @14
    iftrue
    @11
    @15
    @7
    @13
    @35
    eqeq1d
    syl5ib
    @16
    @36
    @11
    @19
    @17
    wceq
    @16
    @17
    @18
    iftrue
    @11
    @5
    @19
    @17
    @11
    @20
    @21
    @34
    simpld
    #
    eqeq1d
    syl5ibr
    syld
    @11
    @36
    wn
    @12
    vm
    vn
    weq
    #
    wn
    #
    wph
    @39
    @3
    @9
    unxpdomlem2.2
    ad2antrr
    @12
    @36
    @38
    vz
    vm
    vn
    equequ1
    notbid
    syl5ibrcom
    pm2.65d
    #
    iffalsed
    @11
    @16
    @12
    @40
    @16
    wn
    @12
    @11
    @19
    @18
    wceq
    @16
    @17
    @18
    iffalse
    @11
    @5
    @19
    @18
    @37
    eqeq1d
    syl5ibr
    mt3d
    3eqtr3d
    mtand
end
