include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "c1.mm"
include "caddc.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cmpt2.mm"
include "eqid.mm"
include "weq.mm"
include "oveq2.mm"
include "feq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "abbii.mm"
include "mpt2eq123i.mm"
include "eqidd.mm"
include "eqeq1.mm"
include "3anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "cbvmpt2v.mm"
include "eqtr3i.mm"
include "sdclem1.mm"

theorem sdc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wsi: wff si
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cJ: class J
  let cF: class F
  let cG: class G
  assume sdc.1: |- Z = ( ZZ>= ` M )
  assume sdc.2: |- ( g = ( f |` ( M ... n ) ) -> ( ps <-> ch ) )
  assume sdc.3: |- ( n = M -> ( ps <-> ta ) )
  assume sdc.4: |- ( n = k -> ( ps <-> th ) )
  assume sdc.5: |- ( ( g = h /\ n = ( k + 1 ) ) -> ( ps <-> si ) )
  assume sdc.6: |- ( ph -> A e. V )
  assume sdc.7: |- ( ph -> M e. ZZ )
  assume sdc.8: |- ( ph -> E. g ( g : { M } --> A /\ ta ) )
  assume sdc.9: |- ( ( ph /\ k e. Z ) -> ( ( g : ( M ... k ) --> A /\ th ) -> E. h ( h : ( M ... ( k + 1 ) ) --> A /\ g = ( h |` ( M ... k ) ) /\ si ) ) )

  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint A g
  disjoint h k
  disjoint h n
  disjoint A h
  disjoint k n
  disjoint A k
  disjoint A n
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M k
  disjoint M n
  disjoint ch g
  disjoint f ps
  disjoint h ps
  disjoint k ps
  disjoint f si
  disjoint g si
  disjoint n si
  disjoint n ph
  disjoint n th
  disjoint V h
  disjoint h ta
  disjoint k ta
  disjoint n ta
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z k
  disjoint Z n
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint g j
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint h j
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint j k
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint h m
  disjoint J h
  disjoint j m
  disjoint J j
  disjoint k m
  disjoint J k
  disjoint m w
  disjoint m x
  disjoint J m
  disjoint J w
  disjoint J x
  disjoint f m
  disjoint g m
  disjoint M j
  disjoint m n
  disjoint m y
  disjoint M m
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint ch j
  disjoint F j
  disjoint F m
  disjoint F n
  disjoint F w
  disjoint F x
  disjoint j ps
  disjoint ps x
  disjoint ps y
  disjoint j si
  disjoint si x
  disjoint si y
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G w
  disjoint G x
  disjoint j ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint th w
  disjoint th x
  disjoint th y
  disjoint j ta
  disjoint ta w
  disjoint ta x
  disjoint ta y
  disjoint Z j
  disjoint Z m
  disjoint Z w
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> E. f ( f : Z --> A /\ A. n e. Z ch ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wsi
    vx
    vy
    cA
    vf
    vg
    vh
    vk
    vn
    vj
    vf
    cZ
    cM
    vk
    cv
    #
    cfz
    co
    #
    cA
    vg
    cv
    #
    wf
    #
    wth
    wa
    #
    vk
    cZ
    wrex
    #
    vg
    cab
    #
    cM
    @0
    c1
    caddc
    co
    cfz
    co
    cA
    vh
    cv
    #
    wf
    #
    vf
    cv
    #
    @7
    @1
    cres
    #
    wceq
    #
    wsi
    w3a
    #
    vk
    cZ
    wrex
    #
    vh
    cab
    #
    cmpt2
    #
    cM
    vn
    cv
    #
    cfz
    co
    #
    cA
    @2
    wf
    #
    wps
    wa
    #
    vn
    cZ
    wrex
    #
    vg
    cab
    #
    cM
    cV
    cZ
    sdc.1
    sdc.2
    sdc.3
    sdc.4
    sdc.5
    sdc.6
    sdc.7
    sdc.8
    sdc.9
    @21
    eqid
    vj
    vf
    cZ
    @21
    @14
    cmpt2
    @15
    vy
    vx
    cZ
    @21
    @8
    vx
    cv
    #
    @10
    wceq
    #
    wsi
    w3a
    #
    vk
    cZ
    wrex
    #
    vh
    cab
    #
    cmpt2
    vj
    vf
    cZ
    @21
    @14
    cZ
    @6
    @14
    cZ
    eqid
    @20
    @5
    vg
    @19
    @4
    vn
    vk
    cZ
    vn
    vk
    weq
    #
    @18
    @3
    wps
    wth
    @27
    @17
    @1
    cA
    @2
    @16
    @0
    cM
    cfz
    oveq2
    feq2d
    sdc.4
    anbi12d
    cbvrexv
    abbii
    @14
    eqid
    mpt2eq123i
    vj
    vf
    vy
    vx
    cZ
    @21
    @14
    @26
    @14
    vj
    vy
    weq
    @14
    eqidd
    vf
    vx
    weq
    #
    @13
    @25
    vh
    @28
    @12
    @24
    vk
    cZ
    @28
    @11
    @23
    @8
    wsi
    @9
    @22
    @10
    eqeq1
    3anbi2d
    rexbidv
    abbidv
    cbvmpt2v
    eqtr3i
    sdclem1
end
