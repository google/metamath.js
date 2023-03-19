include "cr.mm"
include "crrh.mm"
include "cfv.mm"
include "wf.mm"
include "cuni.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "eqid.mm"
include "rrhcn.mm"
include "uniretop.mm"
include "cnf.mm"
include "syl.mm"
include "cxme.mm"
include "ctps.mm"
include "wceq.mm"
include "cnrg.mm"
include "cngp.mm"
include "nrgngp.mm"
include "ngpxms.mm"
include "3syl.mm"
include "xmstps.mm"
include "tpsuni.mm"
include "feq3d.mm"
include "mpbird.mm"

theorem rrhf
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cJ: class J
  let cK: class K
  let cZ: class Z
  assume rrhf.d: |- D = ( ( dist ` R ) |` ( B X. B ) )
  assume rrhf.j: |- J = ( topGen ` ran (,) )
  assume rrhf.b: |- B = ( Base ` R )
  assume rrhf.k: |- K = ( TopOpen ` R )
  assume rrhf.z: |- Z = ( ZMod ` R )
  assume rrhf.1: |- ( ph -> R e. DivRing )
  assume rrhf.2: |- ( ph -> R e. NrmRing )
  assume rrhf.3: |- ( ph -> Z e. NrmMod )
  assume rrhf.4: |- ( ph -> ( chr ` R ) = 0 )
  assume rrhf.5: |- ( ph -> R e. CUnifSp )
  assume rrhf.6: |- ( ph -> ( UnifSt ` R ) = ( metUnif ` D ) )


  assert |- ( ph -> ( RRHom ` R ) : RR --> B )

  proof
    wph
    cr
    cB
    cR
    crrh
    cfv
    #
    wf
    cr
    cK
    cuni
    #
    @0
    wf
    #
    wph
    @0
    cioo
    crn
    ctg
    cfv
    #
    cK
    ccn
    co
    wcel
    @2
    wph
    cB
    cD
    cR
    @3
    cK
    cZ
    rrhf.d
    @3
    eqid
    rrhf.b
    rrhf.k
    rrhf.z
    rrhf.1
    rrhf.2
    rrhf.3
    rrhf.4
    rrhf.5
    rrhf.6
    rrhcn
    @0
    @3
    cK
    cr
    @1
    uniretop
    @1
    eqid
    cnf
    syl
    wph
    cB
    @1
    @0
    cr
    wph
    cR
    cxme
    wcel
    #
    cR
    ctps
    wcel
    cB
    @1
    wceq
    wph
    cR
    cnrg
    wcel
    cR
    cngp
    wcel
    @4
    rrhf.2
    cR
    nrgngp
    cR
    ngpxms
    3syl
    cR
    xmstps
    cB
    cK
    cR
    rrhf.b
    rrhf.k
    tpsuni
    3syl
    feq3d
    mpbird
end
